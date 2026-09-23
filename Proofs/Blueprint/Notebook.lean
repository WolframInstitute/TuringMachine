/-
  Blueprint.Notebook

  Computational footnotes in the blueprint. `:::notebook "Lean.Name"` after a
  node marks the Wolfram notebook of that declaration: the footnote written
  in `Blueprint/Notebooks/<Lean.Name>.md` and deployed by
  `scripts/CloudDeployNotebooks.wl` as a public cloud notebook with a PNG
  preview. The directive fails the build when the footnote file is missing.

  In the HTML the marker is a button under the node. It opens a panel on the
  right (a sheet at the bottom on narrow screens) that shows the preview and,
  on request, the live notebook through `wolfram-notebook-embedder`. While
  the panel is open it follows the footnote nearest the top of the window
  unless it is pinned.
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
.wl-nb { margin: 0.4em 0 1.2em; }
.wl-nb-chip {
  font: inherit; font-size: 0.85em; cursor: pointer;
  border: 1px solid #c6282833; border-radius: 1em; padding: 0.15em 0.8em;
  background: #fff4f2; color: #b22222;
}
.wl-nb-chip:hover { background: #ffe4df; }
#wl-nb-panel {
  position: fixed; top: 0; right: 0; bottom: 0; width: min(44vw, 680px);
  display: flex; flex-direction: column; z-index: 1000;
  background: #fff; color: #222; border-left: 1px solid #ddd;
  box-shadow: -4px 0 16px #0002; transform: translateX(105%);
  transition: transform 0.2s ease-out;
}
body.wl-nb-open #wl-nb-panel { transform: none; }
body.wl-nb-open { padding-right: min(44vw, 680px); }
#wl-nb-panel header {
  display: flex; align-items: center; gap: 0.5em; padding: 0.5em 0.8em;
  border-bottom: 1px solid #ddd; font-size: 0.9em;
}
#wl-nb-panel header .wl-nb-title { flex: 1; font-family: monospace; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
#wl-nb-panel header button, #wl-nb-panel header a {
  font: inherit; cursor: pointer; background: none; border: 1px solid #ccc;
  border-radius: 0.3em; padding: 0.1em 0.5em; color: inherit; text-decoration: none;
}
#wl-nb-panel header button[aria-pressed="true"] { background: #eee; }
#wl-nb-panel .wl-nb-body { flex: 1; overflow: auto; padding: 0.5em; }
#wl-nb-panel .wl-nb-body img { width: 100%; height: auto; display: block; }
#wl-nb-panel .wl-nb-note { color: #666; font-size: 0.85em; padding: 0.3em 0.2em; }
@media (max-width: 900px) {
  #wl-nb-panel { top: auto; left: 0; width: 100vw; height: 70vh; border-left: 0;
    border-top: 1px solid #ddd; transform: translateY(105%); }
  body.wl-nb-open { padding-right: 0; }
}
@media (prefers-color-scheme: dark) {
  #wl-nb-panel { background: #1e1e1e; color: #ddd; border-color: #444; }
  #wl-nb-panel header { border-color: #444; }
  .wl-nb-chip { background: #3a1f1f; color: #ffb4a8; }
}
@media print { #wl-nb-panel, .wl-nb-chip { display: none; } }
"#

def notebookJs : String := r#"
(function () {
  const EMBEDDER = "https://cdn.jsdelivr.net/npm/wolfram-notebook-embedder@0.3.0/dist/wolfram-notebook-embedder.min.js";
  let panel, current = null, pinned = false, embedding = null, embedderLoading = null;

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

  function buildPanel() {
    panel = el("aside", { id: "wl-nb-panel", "aria-label": "Computational footnote" });
    const header = el("header");
    header.append(el("span", { class: "wl-nb-title" }));
    const live = el("button", { type: "button", class: "wl-nb-live" }, "Live");
    live.title = "Load the live notebook";
    live.onclick = () => showLive();
    const pin = el("button", { type: "button", class: "wl-nb-pin", "aria-pressed": "false" }, "Pin");
    pin.title = "Keep this notebook while scrolling";
    pin.onclick = () => { pinned = !pinned; pin.setAttribute("aria-pressed", String(pinned)); };
    const open = el("a", { class: "wl-nb-open", target: "_blank", rel: "noopener" }, "Cloud");
    open.title = "Open in the Wolfram Cloud";
    const close = el("button", { type: "button", "aria-label": "Close" }, "×");
    close.onclick = () => document.body.classList.remove("wl-nb-open");
    header.append(live, pin, open, close);
    panel.append(header, el("div", { class: "wl-nb-body" }));
    document.body.append(panel);
  }

  function show(marker) {
    if (!panel) buildPanel();
    if (current === marker) { document.body.classList.add("wl-nb-open"); return; }
    current = marker;
    if (embedding) { embedding.then(e => e.detach()).catch(() => {}); embedding = null; }
    const label = marker.dataset.label, url = marker.dataset.nb;
    panel.querySelector(".wl-nb-title").textContent = label;
    panel.querySelector(".wl-nb-open").href = url;
    const body = panel.querySelector(".wl-nb-body");
    body.replaceChildren(
      el("img", { src: marker.dataset.preview, alt: "Notebook for " + label, loading: "lazy" }),
      el("div", { class: "wl-nb-note" }, "Preview. Press Live to load the notebook itself."));
    document.body.classList.add("wl-nb-open");
  }

  function showLive() {
    if (!current) return;
    const body = panel.querySelector(".wl-nb-body");
    const node = el("div");
    body.replaceChildren(node);
    embedding = loadEmbedder().then(E => E.embed(current.dataset.nb, node, { allowInteract: true }));
    embedding.catch(() => {
      body.replaceChildren(el("div", { class: "wl-nb-note" },
        "The live notebook could not be loaded here; use the Cloud link."));
    });
  }

  function follow() {
    const markers = Array.from(document.querySelectorAll(".wl-nb"));
    const observer = new IntersectionObserver(entries => {
      if (pinned || !document.body.classList.contains("wl-nb-open")) return;
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
      let preview := notebookBase ++ label ++ ".png"
      pure <| .tag "div" #[("class", "wl-nb"), ("data-label", label), ("data-nb", url),
          ("data-preview", preview)] <|
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
