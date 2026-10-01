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
Display every strict edge between shown vertices with an arrow. All remaining
unspecified off-diagonal cells are optional normal natural edges. Use an
explicit exterior cell for each displayed pair which is not natural.
Gray always means outside the path; it never denotes an absent selection
or a choice of weighting.

For a whole ordinary diagram, supply its area sequence to draw the boundary and shade
the exterior automatically:

```tex
\LLTAreaDiagram[condition={A\in C}]{0,1,2,3}{0,1,2,1}{
  \LLTStrict{1}{3}
  \LLTStrict{3}{4}
}
```

The label and area lists must have equal lengths; area entries are integers
with `0 <= a_i <= i` and `a_(i+1) <= a_i+1`. The command checks these bounds.
Its final argument adds restrictions using the same cell commands. Supply
only restrictions compatible with the specified natural edges; the renderer
does not verify strict-corner or cover conditions. A label such as `5` can
occupy position one: the area sequence uses positions, not numerical labels.

| Command inside the diagram | Meaning | Cell entry |
| --- | --- | --- |
| `\LLTOptional{i}{j}` | Natural normal edge, freely selected or absent | Blank |
| `\LLTSelected{i}{j}` | Selected normal edge | `1` |
| `\LLTAbsent{i}{j}` | Natural normal edge, absent from the selection | `0` |
| `\LLTForbidden{i}{j}` | No natural edge | Gray exterior |
| `\LLTStrict{i}{j}` | Strict edge, always selected | Arrow |
| `\LLTSelected*{i}{j}` | Selected normal edge which is a cover | Underlined `1` |
| `\LLTStrict*{i}{j}` | Strict edge which is a cover | Underlined arrow |
| `\LLTCell{i}{j}{entry}` | Custom restriction defined in the accompanying text | Supplied entry |

Cover conditions concern the full selected relation, including the exterior.
Use `condition={...}` for layer size, connectedness, a component, endpoint
colors or other global restrictions. Use `name={...}` for a mathematical
label above the diagram. These annotations describe the set being summed.

The surrounding formula specifies whether the sum is weighted. The
`weighted=true` option records the convention `q^{|A\setminus S|}` but
changes no shading. Both weighted and unweighted diagrams have white natural
cells and a gray exterior. Entries and vertex labels are plain, with no
boxes or colored circles.

Use `gaps={1,3}` to put a zigzag after the first and third displayed vertex.
This suppresses an arbitrary intervening interval, which may be empty;
leave no gap between vertices required to be consecutive. In the NN and DN
macros the two contact vertices share consecutive steps. In the diamond
macro neither pair is required to be consecutive, so both gaps are shown.
Whole area diagrams use the supplied ordered list as their rank order.

Style keys are `cell size`, `label font`, `entry font`, `gaps` and `gap size`.
Set defaults with `\LLTDiagramSetup{cell size=6mm}`; per-diagram options are
local. The convenience commands
`\LLTSelectionTriangle[options]{labels}{bit}{bit}`, `\LLTNNSource`,
`\LLTNNTarget`, `\LLTDNSource` and `\LLTDNTarget` all use
the same renderer and restrictions. The NN commands take three ordered
labels; DN takes four. A triangle's long edge is selected normal, with
the two short bits fixed as supplied.

`diagram-examples.tex` is a legend and mathematical usage guide.
`intro-flip.tex` shows the smallest whole flip component and its HRV fibres.
`ordinary-diamond.tex` and `layer-relations.tex` generate the draft's SVGs.
`prefix-attachment.tex` shows component-restricted sums glued at a fixed
endpoint color. Its right factor omits the shared vertex weight, as indicated
by `\widehat V`; the surrounding statement defines this valuation.
`crossing-sweeps.tex` shows four fully specified selected states and the six
actual flips between them, including the restoration of the exterior.
`two-chain-packing.tex` uses these crossing slides to rearrange two selected
good edges between the same pair of corner chains.
`complete-child-merge.tex` displays the four flips replacing one child edge
by an edge between two children, with the common exterior fixed at endpoints.
`last-clique-tree.tex` fixes every natural cell to show a core tree and the
full tree obtained by attaching the omitted vertices as leaves. Each picture
therefore denotes a single selected state; additional good edges are supplied
in the accompanying proof.
`circular-dd-elimination.tex` displays the weighted restricted-sum identity
`q F(D) = F(R) - F(E)` for a DD contact. Its blank cells remain optional;
the accompanying caption specifies the coloring or admissible HRV valuation.
`circular-direct-relations.tex` collects all four weighted recurrences as
generic local boundary paths. The author-supplied Robin source snapshot is
in `references/alexandersson-sulzgruber-2022/`; its `SOURCE.md` records the
original host location. The local path pictures in the earlier
Alexandersson--Dai `Circular Vertical-Strip LLT Polynomials-v9.tex` were also
consulted read-only. Zigzags denote arbitrary unchanged portions; the adjacent
contact vertices share steps. Gray is outside the path, and the red line is
the bounce. No fixed small area sequence is substituted for the general
contact geometry.
`initial-crossing.tex` uses the same cells for the crossing-slide endpoints.
`circular-reversal.tex` and `right-attachment.tex` give native TikZ sources
for the column permutation and fibre concatenation. Every manuscript figure
now has a native TeX source. `circular-companion.tex` illustrates a finite
companion deletion and the same balanced path in compatible lift order.
Its two pictures specify individual selections, the singleton case of the
restricted-sum convention.
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
latexmk -pdf -interaction=nonstopmode -halt-on-error prefix-attachment.tex
pdftocairo -svg prefix-attachment.pdf prefix-attachment.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error crossing-sweeps.tex
pdftocairo -svg crossing-sweeps.pdf crossing-sweeps.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error two-chain-packing.tex
pdftocairo -svg two-chain-packing.pdf two-chain-packing.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error complete-child-merge.tex
pdftocairo -svg complete-child-merge.pdf complete-child-merge.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error last-clique-tree.tex
pdftocairo -svg last-clique-tree.pdf last-clique-tree.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error circular-dd-elimination.tex
pdftocairo -svg circular-dd-elimination.pdf circular-dd-elimination.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error circular-direct-relations.tex
pdftocairo -svg circular-direct-relations.pdf circular-direct-relations.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error initial-crossing.tex
pdftocairo -svg initial-crossing.pdf initial-crossing.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error circular-reversal.tex
pdftocairo -svg circular-reversal.pdf circular-reversal.svg
latexmk -pdf -interaction=nonstopmode -halt-on-error right-attachment.tex
pdftocairo -svg right-attachment.pdf right-attachment.svg
```

The previous external `LLTCells` macro was inspected for diagonal-label
orientation. Its gray/white weighting convention is superseded here by the
author's instruction: gray denotes the exterior of the path. The external manuscript
has not been modified. This package supplies the sum restrictions for the
new draft and should be loaded independently of the old figure definitions.
