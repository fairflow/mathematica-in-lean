/-
Graphics in the infoview — Rob Lewis's second suggested Lean 4 improvement:
"the widget framework in Lean 4 is more powerful and perhaps there's a less hackish
way of displaying graphs and images generated from Mathematica."

`#mathematica_plot "Plot[...]"` asks the (headless) kernel to rasterise a graphic to
a PNG, base64-encodes it, and renders it as an `<img>` in the Lean infoview using
ProofWidgets (which ships as a dependency via mathlib — no new deps).

Works for anything Mathematica can `Export` to PNG: `Plot`, `Plot3D`,
`ContourPlot`, `Graphics`, `Graphics3D`, `Histogram`, …
-/
import Mathematica.Tactic
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Command ProofWidgets

namespace Mathematica

/-- `#mathematica_plot "Plot[...]"` renders a Mathematica graphic in the infoview. -/
syntax (name := mmPlot) "#mathematica_plot " str : command

@[command_elab mmPlot]
def elabMmPlot : CommandElab := fun
  | `(#mathematica_plot $s:str) => do
      -- ask the kernel for a PNG data URL
      let url ← liftTermElabM do
        let code := "\"data:image/png;base64,\" <> ExportString[ExportString["
          ++ s.getString ++ ", \"PNG\"], \"Base64\"]"
        match ← executeAndEval (← defaultTransport) code with
        | .str u => pure u
        | other  => throwError m!"#mathematica_plot: expected an image data URL, got {toString other}"
      -- render it as an <img> in the infoview
      let img : Html := .element "img" #[("src", Json.str url)] #[]
      logInfo (← liftCoreM <| Lean.MessageData.ofHtml img "Mathematica plot (open in the Lean infoview)")
  | _ => throwError "unexpected #mathematica_plot syntax"

end Mathematica
