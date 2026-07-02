//! Self-describing autodiscovery loader — lets the paclet load its functions
//! with plain built-in Wolfram Language, no ExtensionCargo / PacletExtensions.
//!
//! `rustlink_autodiscover_wxf(lib_path)` returns the WXF of
//! ```wolfram
//! <| name -> LibraryFunctionLoad[lib_path, name, {argtypes}, rettype], ... |>
//! ```
//! for every `#[wll::export]` function, with the *literal* library path baked
//! in. The Wolfram side deserializes it and the `LibraryFunctionLoad` calls
//! evaluate straight into loaded `LibraryFunction`s:
//! ```wolfram
//! functions = BinaryDeserialize[ByteArray[Normal[loader[lib_path]]]]
//! ```
//!
//! Signatures come from the `#[wll::export]` inventory (via each entry's
//! `signature()` closure), so nothing here is hand-maintained. This is the same
//! data `exported_library_functions_association` uses, but emitted in a flat,
//! literal-path form instead of its `With[{lib}, …]` / `NativeCaller` shape,
//! which only unpacks through ExtensionCargo's `HoldRest` extraction.
//!
//! Note: exported functions must take `DataStore` by value, not `&DataStore`
//! (whose `parameter_type()` panics), or the `signature()` calls abort.

use wolfram_library_link as wll;
use wolfram_serialize::constants::HeaderEnum;
use wolfram_serialize::{ToWXF, Writer, WxfWriter};

/// The loader itself is exported too; omit it from the discovered set so the
/// paclet's function table holds only the real library functions.
const LOADER_NAME: &str = "rustlink_autodiscover_wxf";

/// Build the WXF payload `<|name -> LibraryFunctionLoad[lib_path, name, {args}, ret]|>`.
pub fn autodiscover_wxf_bytes(lib_path: &str) -> Vec<u8> {
    let buf = vec![HeaderEnum::Version as u8, HeaderEnum::Separator as u8];
    let mut w = WxfWriter::new(buf);
    build(&mut w, lib_path).expect("autodiscover WXF serialization is infallible over a Vec");
    w.into_inner()
}

fn build<W: Writer>(w: &mut WxfWriter<W>, lib_path: &str) -> Result<(), wolfram_serialize::Error> {
    // Native `#[export]`s whose signature resolves, minus the loader itself.
    let entries: Vec<(&'static str, Vec<_>, _)> = wll::inventory::iter::<wll::macro_utils::LibraryLinkFunction>()
        .filter_map(|entry| match entry {
            wll::macro_utils::LibraryLinkFunction::Native { name, signature } if *name != LOADER_NAME => {
                signature().ok().map(|(params, ret)| (*name, params, ret))
            },
            _ => None,
        })
        .collect();

    w.write_association(entries.len())?;
    for (name, params, ret) in &entries {
        w.write_rule(false)?; // Rule (->): evaluate LibraryFunctionLoad on deserialize
        w.write_string(name)?; // key
        // value: LibraryFunctionLoad[lib_path, name, {argtypes}, rettype]
        w.write_function(4)?;
        w.write_symbol("System`LibraryFunctionLoad")?;
        w.write_string(lib_path)?;
        w.write_string(name)?;
        w.write_function(params.len())?;
        w.write_symbol("System`List")?;
        for p in params {
            p.to_wxf(w)?;
        }
        ret.to_wxf(w)?;
    }
    Ok(())
}
