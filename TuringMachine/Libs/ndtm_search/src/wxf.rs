//! WXF encoding for the table types this library returns to Wolfram Language.
//!
//! Token writing is delegated to [`wolfram_serialize::WxfWriter`]; this module
//! only fixes the encoding policy the WL side of the paclet relies on:
//! `Option::None` is the bare symbol `None` (and `Some(v)` is just `v`),
//! tuples are `List[...]`, and `BigUint`/`BigInt` are WXF big-integer tokens.
//! (The `ToWXF` trait in `wolfram-serialize` instead encodes `Option` in its
//! enum wire form, so it is not used here.)

use num_bigint::{BigInt, BigUint};
use wolfram_serialize::constants::HeaderEnum;
use wolfram_serialize::{Error, Writer, WxfWriter};

/// Types encodable in the paclet's WXF convention.
pub trait WxfEncode {
    /// Write `self` as WXF tokens.
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error>;
}

/// Serialize a value to a complete uncompressed WXF blob (`8:` header + body).
pub fn to_wxf_bytes<T: WxfEncode>(value: &T) -> Result<Vec<u8>, Error> {
    let buf = vec![HeaderEnum::Version as u8, HeaderEnum::Separator as u8];
    let mut w = WxfWriter::new(buf);
    value.encode(&mut w)?;
    Ok(w.into_inner())
}

fn write_list_header<W: Writer>(w: &mut WxfWriter<W>, len: usize) -> Result<(), Error> {
    w.write_function(len)?;
    w.write_symbol("List")
}

macro_rules! impl_encode_int {
    ($($t:ty),*) => { $(
        impl WxfEncode for $t {
            fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
                w.write_integer(*self as i64)
            }
        }
    )* }
}
impl_encode_int!(i8, i16, i32, i64, u8, u16, u32, u64, usize);

impl WxfEncode for f64 {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> { w.write_real(*self) }
}
impl WxfEncode for bool {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        w.write_symbol(if *self { "True" } else { "False" })
    }
}
impl WxfEncode for str {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> { w.write_string(self) }
}
impl WxfEncode for String {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> { w.write_string(self) }
}
impl WxfEncode for BigInt {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        w.write_big_integer(&self.to_string())
    }
}
impl WxfEncode for BigUint {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        w.write_big_integer(&self.to_string())
    }
}

impl<T: WxfEncode> WxfEncode for Option<T> {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        match self {
            Some(v) => v.encode(w),
            None => w.write_symbol("None"),
        }
    }
}

impl<T: WxfEncode> WxfEncode for Vec<T> {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        write_list_header(w, self.len())?;
        for item in self {
            item.encode(w)?;
        }
        Ok(())
    }
}
impl<T: WxfEncode> WxfEncode for [T] {
    fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
        write_list_header(w, self.len())?;
        for item in self {
            item.encode(w)?;
        }
        Ok(())
    }
}

macro_rules! impl_encode_tuple {
    ($len:expr => $($T:ident . $idx:tt),+) => {
        impl<$($T: WxfEncode),+> WxfEncode for ($($T,)+) {
            fn encode<W: Writer>(&self, w: &mut WxfWriter<W>) -> Result<(), Error> {
                write_list_header(w, $len)?;
                $( self.$idx.encode(w)?; )+
                Ok(())
            }
        }
    };
}
impl_encode_tuple!(2 => A.0, B.1);
impl_encode_tuple!(3 => A.0, B.1, C.2);
impl_encode_tuple!(4 => A.0, B.1, C.2, D.3);
impl_encode_tuple!(5 => A.0, B.1, C.2, D.3, E.4);
impl_encode_tuple!(6 => A.0, B.1, C.2, D.3, E.4, F.5);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_of_small_ints() {
        let bytes = to_wxf_bytes(&vec![1i64, 2, 3]).unwrap();
        assert_eq!(
            bytes,
            [
                b"8:".as_slice(),
                &[b'f', 3],
                &[b's', 4], b"List",
                &[b'C', 1], &[b'C', 2], &[b'C', 3],
            ]
            .concat()
        );
    }

    #[test]
    fn option_none_is_bare_symbol() {
        let bytes = to_wxf_bytes(&Option::<u64>::None).unwrap();
        assert_eq!(bytes, [b"8:".as_slice(), &[b's', 4], b"None"].concat());
        let some = to_wxf_bytes(&Some(5u64)).unwrap();
        assert_eq!(some, [b"8:".as_slice(), &[b'C', 5]].concat());
    }

    #[test]
    fn tuple_is_list_and_biguint_is_bigint_token() {
        let bytes = to_wxf_bytes(&(42u64, BigUint::from(100u32))).unwrap();
        assert_eq!(
            bytes,
            [
                b"8:".as_slice(),
                &[b'f', 2],
                &[b's', 4], b"List",
                &[b'C', 42],
                &[b'I', 3], b"100",
            ]
            .concat()
        );
    }

    #[test]
    fn nested_table_cell_shapes() {
        // One row of a Vec<Vec<Option<(u64, BigUint)>>> table: {{None, {7, 12}}}
        let table: Vec<Vec<Option<(u64, BigUint)>>> =
            vec![vec![None, Some((7, BigUint::from(12u32)))]];
        let bytes = to_wxf_bytes(&table).unwrap();
        assert_eq!(
            bytes,
            [
                b"8:".as_slice(),
                &[b'f', 1], &[b's', 4], b"List",
                &[b'f', 2], &[b's', 4], b"List",
                &[b's', 4], b"None",
                &[b'f', 2], &[b's', 4], b"List",
                &[b'C', 7],
                &[b'I', 2], b"12",
            ]
            .concat()
        );
    }
}
