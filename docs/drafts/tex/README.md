# Diagrams as restricted sums

Load `llt-diagrams.sty`. The main command is

```tex
\LLTDiagram[condition={|A|=s,\ \kappa(c)=\beta}]{a,b,c}{
  \LLTStrict{1}{3}
  \LLTSelected{1}{2}
}
```

This denotes the sum over permitted selections with `ac` strict, `ab`
selected and `bc` optional, subject to the displayed conditions. The
surrounding text chooses the valuation (`K`, `E`, or another defined value)
and specifies the ambient diagram and exterior. Suppressing a vertex in a
local picture imposes no restriction on its incident edges.

Labels are mathematical expressions. Cell arguments are **positions** in
the ordered label list, starting at one; cell `(i,j)` represents the edge
from label `i` to label `j`, with `i<j`. The macro checks these bounds.
All unspecified off-diagonal cells are optional natural edges. Use an
explicit forbidden cell for each displayed pair which is not natural.

| Command inside the diagram | Meaning | Cell entry |
| --- | --- | --- |
| `\LLTOptional{i}{j}` | Natural normal edge, freely selected or absent | Blank |
| `\LLTSelected{i}{j}` | Selected normal edge | `1` |
| `\LLTAbsent{i}{j}` | Natural normal edge, absent from the selection | `0` |
| `\LLTForbidden{i}{j}` | No natural edge | Cross |
| `\LLTStrict{i}{j}` | Strict edge, always selected | Arrow |
| `\LLTSelected*{i}{j}` | Selected normal edge which is a cover | Underlined `1` |
| `\LLTStrict*{i}{j}` | Strict edge which is a cover | Underlined arrow |
| `\LLTCell[fill]{i}{j}{entry}` | Custom restriction defined in the accompanying text | Supplied entry |

Cover conditions concern the full selected relation, including the exterior.
Use `condition={...}` for layer size, connectedness, a component, endpoint
colors or other global restrictions. Use `name={...}` for a mathematical
label above the diagram. These annotations describe the set being summed.

The default is an unweighted sum of state values; all off-diagonal cells
are gray. With `weighted=true`, selections have weight
`q^{|A\setminus S|}`. Optional and selected normal cells are then white;
strict, absent and forbidden cells remain gray. The surrounding statement
must specify the mode, so its meaning does not rely on color alone.

Style keys are `cell size`, `label font` and `entry font`. Set defaults with
`\LLTDiagramSetup{cell size=6mm}`; per-diagram options are local. The
convenience commands `\LLTSelectionTriangle[options]{labels}{bit}{bit}`,
`\LLTNNSource`, `\LLTNNTarget`, `\LLTDNSource` and `\LLTDNTarget` all use
the same renderer and restrictions. The NN commands take three ordered
labels; DN takes four. A triangle's long edge is selected normal, with
the two short bits fixed as supplied.

`diagram-examples.tex` is a two-page legend and mathematical usage guide.
`ordinary-diamond.tex` and `layer-relations.tex` generate the draft's SVGs.
An equation between diagrams means equality of the indicated sums. A
flip-path arrow is stated separately as a correspondence between endpoint
states; it does not assert equality of their individual valuations.

Build from a copied source directory in the external request cache:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error diagram-examples.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error ordinary-diamond.tex
pdftocairo -svg ordinary-diamond.pdf ordinary-diamond.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error layer-relations.tex
pdftocairo -svg layer-relations.pdf layer-relations.svg
```

The previous external `LLTCells` macro was inspected for the diagonal-label
orientation and gray/white weighting convention. The external manuscript
has not been modified. This package supplies the sum restrictions for the
new draft and should be loaded independently of the old figure definitions.
