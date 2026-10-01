/-
  Blueprint.Notebook

  Computational footnotes in the blueprint. `:::notebook "Lean.Name"` after a
  node marks the Wolfram notebook of that declaration: the footnote written
  in `Blueprint/Notebooks/<Lean.Name>.md` and deployed by
  `scripts/CloudDeployNotebooks.wl` as a public cloud notebook. The directive
  fails the build when the footnote file is missing.

  In the HTML the marker is a button under the node. It opens a panel on the
  right (a sheet at the bottom on narrow screens) with the notebook embedded
  by `wolfram-notebook-embedder`; the border between the text and the panel
  can be dragged, and the width is remembered. While the panel is open it
  follows the footnote nearest the top of the window.
-/

import VersoManual

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output (Html)

namespace Blueprint

/-- Where the footnotes are deployed. -/
def notebookBase : String :=
  "https://www.wolframcloud.com/obj/wolframinstitute/wolfram23-blueprint/notebooks/"

def notebookCss : String := r#"
:root { --wl-nb-width: min(44vw, 680px); }
.wl-nb { margin: 0.4em 0 1.2em; }
.wl-nb-chip {
  font: inherit; font-size: 0.85em; cursor: pointer;
  border: 1px solid #c6282833; border-radius: 1em; padding: 0.15em 0.8em;
  background: #fff4f2; color: #b22222;
}
.wl-nb-chip:hover { background: #ffe4df; }
#wl-nb-panel {
  position: fixed; top: 0; right: 0; bottom: 0; width: var(--wl-nb-width);
  z-index: 1000; background: #fff; border-left: 1px solid #ddd;
  box-shadow: -4px 0 16px #0002; transform: translateX(105%);
  transition: transform 0.2s ease-out;
}
body.wl-nb-open #wl-nb-panel { transform: none; }
body.wl-nb-open { padding-right: var(--wl-nb-width); }
body.wl-nb-resizing, body.wl-nb-resizing * { cursor: col-resize !important; user-select: none; }
body.wl-nb-resizing #wl-nb-panel { transition: none; }
#wl-nb-panel .wl-nb-body { position: absolute; inset: 0 0 0 6px; overflow: auto; }
#wl-nb-panel .wl-nb-grip {
  position: absolute; top: 0; bottom: 0; left: -3px; width: 9px; cursor: col-resize; z-index: 2;
}
#wl-nb-panel .wl-nb-grip:hover, body.wl-nb-resizing .wl-nb-grip { background: #b2222233; }
#wl-nb-panel .wl-nb-close {
  position: absolute; top: 6px; right: 10px; z-index: 3; cursor: pointer;
  font: 18px/1 sans-serif; width: 26px; height: 26px; border-radius: 13px;
  border: 1px solid #ccc; background: #fffc; color: #555;
}
#wl-nb-panel .wl-nb-note { color: #666; font-size: 0.85em; padding: 1em; }
@media (max-width: 900px) {
  #wl-nb-panel { top: auto; left: 0; width: 100vw; height: 70vh; border-left: 0;
    border-top: 1px solid #ddd; transform: translateY(105%); }
  body.wl-nb-open { padding-right: 0; }
  #wl-nb-panel .wl-nb-grip { display: none; }
  #wl-nb-panel .wl-nb-body { left: 0; }
}
@media print { #wl-nb-panel, .wl-nb-chip { display: none; } }
"#

def notebookJs : String := r#"
(function () {
  const EMBEDDER = "https://cdn.jsdelivr.net/npm/wolfram-notebook-embedder@0.3.0/dist/wolfram-notebook-embedder.min.js";
  const WIDTH_KEY = "wl-nb-width";
  let panel, body, current = null, embedding = null, embedderLoading = null;

  function loadEmbedder() {
    if (window.WolframNotebookEmbedder) return Promise.resolve(window.WolframNotebookEmbedder);
    if (!embedderLoading) {
      embedderLoading = new Promise((resolve, reject) => {
        const s = document.createElement("script");
        s.src = EMBEDDER; s.crossOrigin = "anonymous";
        s.onload = () => resolve(window.WolframNotebookEmbedder);
        s.onerror = reject;
        document.head.appendChild(s);
      });
    }
    return embedderLoading;
  }

  function el(tag, attrs, text) {
    const e = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs || {})) e.setAttribute(k, v);
    if (text) e.textContent = text;
    return e;
  }

  function setWidth(px) {
    const w = Math.max(280, Math.min(px, window.innerWidth - 320));
    document.documentElement.style.setProperty("--wl-nb-width", w + "px");
    return w;
  }

  function buildPanel() {
    panel = el("aside", { id: "wl-nb-panel", "aria-label": "Computational footnote" });
    const grip = el("div", { class: "wl-nb-grip", role: "separator", "aria-orientation": "vertical",
      title: "Drag to resize" });
    const close = el("button", { type: "button", class: "wl-nb-close", "aria-label": "Close" }, "×");
    close.onclick = () => document.body.classList.remove("wl-nb-open");
    body = el("div", { class: "wl-nb-body" });
    panel.append(grip, close, body);
    document.body.append(panel);
    try { const w = parseInt(localStorage.getItem(WIDTH_KEY), 10); if (w) setWidth(w); } catch (e) {}
    grip.addEventListener("pointerdown", ev => {
      ev.preventDefault();
      grip.setPointerCapture(ev.pointerId);
      document.body.classList.add("wl-nb-resizing");
      const move = e => setWidth(window.innerWidth - e.clientX);
      const up = e => {
        const w = setWidth(window.innerWidth - e.clientX);
        try { localStorage.setItem(WIDTH_KEY, String(w)); } catch (err) {}
        document.body.classList.remove("wl-nb-resizing");
        grip.removeEventListener("pointermove", move);
        grip.removeEventListener("pointerup", up);
      };
      grip.addEventListener("pointermove", move);
      grip.addEventListener("pointerup", up);
    });
  }

  function show(marker) {
    if (!panel) buildPanel();
    document.body.classList.add("wl-nb-open");
    if (current === marker) return;
    current = marker;
    if (embedding) { embedding.then(e => e.detach()).catch(() => {}); embedding = null; }
    const note = el("div", { class: "wl-nb-note" }, "Loading the notebook of " + marker.dataset.label + "\u2026");
    const node = el("div");
    body.replaceChildren(note, node);
    embedding = loadEmbedder().then(E => E.embed(marker.dataset.nb, node, { allowInteract: true }));
    embedding.then(() => note.remove(), () => {});
    embedding.catch(() => {
      body.replaceChildren(el("div", { class: "wl-nb-note" }, "The notebook could not be loaded."));
    });
  }

  function follow() {
    const markers = Array.from(document.querySelectorAll(".wl-nb"));
    const observer = new IntersectionObserver(entries => {
      if (!document.body.classList.contains("wl-nb-open")) return;
      const visible = entries.filter(e => e.isIntersecting)
        .sort((a, b) => a.boundingClientRect.top - b.boundingClientRect.top);
      if (visible.length) show(visible[0].target);
    }, { rootMargin: "0px 0px -50% 0px" });
    markers.forEach(m => {
      observer.observe(m);
      m.querySelector(".wl-nb-chip").addEventListener("click", () => show(m));
    });
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", follow);
  else follow();
})();
"#

block_extension Block.notebook (label : String) where
  data := Json.str label
  traverse _ _ _ := pure none
  extraCss := [notebookCss]
  extraJs := [notebookJs]
  toTeX := some fun _ _ _ _ _ => pure .empty
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str label := data
        | Verso.reportError "Expected a string for a notebook" *> pure .empty
      let url := notebookBase ++ label ++ ".nb"
      pure <| .tag "div" #[("class", "wl-nb"), ("data-label", label), ("data-nb", url)] <|
        .tag "button" #[("type", "button"), ("class", "wl-nb-chip"),
            ("title", "Show the Wolfram notebook of " ++ label)]
          (.text true "Notebook")

structure NotebookConfig where
  label : String

section
variable {m : Type → Type} [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

def NotebookConfig.parse : ArgParse m NotebookConfig :=
  NotebookConfig.mk <$> .positional' `label

instance : FromArgs NotebookConfig m := ⟨NotebookConfig.parse⟩

end

/-- `:::notebook "Lean.Name"` places the computational footnote of `Lean.Name`. -/
@[directive]
def notebook : DirectiveExpanderOf NotebookConfig
  | config, _ => do
    let path : System.FilePath := "Blueprint" / "Notebooks" / (config.label ++ ".md")
    unless ← path.pathExists do
      throwError "no computational footnote {path}"
    ``(Verso.Doc.Block.other (Block.notebook $(quote config.label)) #[])

end Blueprint
