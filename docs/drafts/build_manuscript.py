#!/usr/bin/env python3
"""Assemble the canonical Markdown sections and native TeX figures externally.

This is document conversion only; it performs no mathematical computation.
Requires pandoc, latexmk, pdflatex and bibtex on PATH.
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import zipfile


SOURCE = Path(__file__).resolve().parent
PROJECT = next((path for path in SOURCE.parents if (path / "lakefile.toml").exists()), SOURCE)
SECTIONS = [
    ("i", "INTRODUCTION.md"),
    ("c", "CIRCULAR_E_EXPANSION.md"),
    ("o", "ORDINARY_COMPONENT_DIAGRAM_PROOF.md"),
    ("f", "ORDINARY_FLIP_CONNECTIVITY.md"),
    ("cc", "CIRCULAR_COMPONENTS.md"),
    ("k", "CUMULANTS.md"),
    ("a", "AI_STATEMENT.md"),
]
STATEMENT_ENVIRONMENTS = {
    "theorem", "lemma", "proposition", "corollary", "definition", "example",
    "remark", "proof",
}


def run(args, *, text=None, cwd=None):
    return subprocess.run(
        args, input=text, text=True, cwd=cwd, check=True, capture_output=True
    ).stdout


def latex_fragment(ast, blocks):
    doc = {"pandoc-api-version": ast["pandoc-api-version"], "meta": {}, "blocks": blocks}
    return run(["pandoc", "-f", "json", "-t", "latex", "--natbib"], text=json.dumps(doc))


def raw_inline(value):
    return {"t": "RawInline", "c": ["latex", value]}


def walk(value, transform):
    if isinstance(value, list):
        return [walk(item, transform) for item in value]
    if isinstance(value, dict):
        value = {key: walk(item, transform) for key, item in value.items()}
        return transform(value)
    return value


def stringify(inlines):
    return "".join(
        item["c"] if item["t"] == "Str" else " "
        for item in inlines
    )


def assemble_section(prefix, filename):
    ast = json.loads(run([
        "pandoc", "-f", "markdown-implicit_figures-smart+tex_math_single_backslash",
        "-t", "json", str(SOURCE / filename),
    ]))
    source = (SOURCE / filename).read_text()
    tags = re.findall(r"\\tag\{([^}]+)\}", source)
    if len(tags) != len(set(tags)):
        raise ValueError(f"Duplicate equation tags in {filename}")
    equations = {tag: f"eq:{prefix}:{tag.replace(chr(39), 'prime')}" for tag in tags}
    section_number = next(i for i, (key, _) in enumerate(SECTIONS, 1) if key == prefix)
    equation_numbers = {tag: f"{section_number}.{i}" for i, tag in enumerate(tags, 1)}
    figure_numbers = {}
    figure_sources = []
    def collect_figures(source_blocks):
        blocks = []
        iterator = iter(source_blocks)
        for block in iterator:
            if block["t"] == "Div":
                block["c"][1] = collect_figures(block["c"][1])
            if (block["t"] == "Para" and len(block["c"]) == 1
                    and block["c"][0]["t"] == "Image"):
                picture = block["c"][0]["c"][2][0]
                stem = Path(picture).stem
                caption = next(iterator, None)
                if (not caption or caption["t"] != "Para" or not caption["c"]
                        or caption["c"][0]["t"] != "Emph"):
                    raise ValueError(f"Missing figure caption after {picture}")
                match = re.fullmatch(r"Figure (\d+)\.", stringify(caption["c"][0]["c"]))
                if not match:
                    raise ValueError(f"Unrecognised caption for {picture}")
                label = f"fig:{prefix}:{stem}"
                number = match[1]
                if number in figure_numbers:
                    raise ValueError(f"Duplicate figure number {number} in {filename}")
                figure_numbers[number] = label
                figure_sources.append(stem)
                caption["c"] = caption["c"][2:]
                blocks.append({"t": "DraftFigure", "c": [stem, label, caption]})
            else:
                blocks.append(block)
        return blocks

    blocks = collect_figures(ast["blocks"])

    def convert(value):
        kind = value.get("t")
        if kind == "Math":
            value["c"][1] = re.sub(
                r"\\tag\{([^}]+)\}",
                lambda match: r"\tag{" + equation_numbers[match[1]]
                + r"}\label{" + equations[match[1]] + "}", value["c"][1],
            )
        elif kind == "Str":
            if re.fullmatch(r"[A-Za-z]+~", value["c"]):
                return raw_inline(value["c"])
            # References live in prose, so function arguments in math are untouched.
            match = re.fullmatch(r"\(([^)]+)\)([.,;:]?)", value["c"])
            if match and match[1] in equations:
                return raw_inline(r"\eqref{" + equations[match[1]] + "}" + match[2])
        elif kind in ("Para", "Plain"):
            inlines = value["c"]
            for index in range(len(inlines) - 2):
                first, space, last = inlines[index:index + 3]
                if first == {"t": "Str", "c": "Figure"} and space["t"] == "Space":
                    if last["t"] == "Str":
                        match = re.fullmatch(r"(\d+)([.,;:]?)", last["c"])
                        if match:
                            label = figure_numbers[match[1]]
                            inlines[index + 2] = raw_inline(r"\ref{" + label + "}" + match[2])
        elif kind == "Link":
            target = value["c"][2][0]
            if "#" in target:
                file, anchor = target.split("#", 1)
                matches = [key for key, name in SECTIONS if name == file]
                if matches:
                    value["c"][2][0] = "#" + matches[0] + "-" + anchor
        elif kind == "Header":
            value["c"][1][0] = prefix + "-" + value["c"][1][0]
        elif kind == "DraftFigure":
            stem, label, caption = value["c"]
            caption_tex = latex_fragment(ast, [caption]).strip()
            return {"t": "RawBlock", "c": ["latex", (
                "\\begin{figure}[htbp]\n\\centering\n"
                + r"\includegraphics[max width=.98\linewidth]{figures/" + stem + ".pdf}\n"
                + r"\caption{" + caption_tex + "}\n"
                + r"\label{" + label + "}\n\\end{figure}"
            )]}
        elif kind == "Div":
            (label, classes, attributes), contents = value["c"]
            environments = STATEMENT_ENVIRONMENTS.intersection(classes)
            if len(environments) != 1:
                raise ValueError(f"Expected one mathematical environment in {filename}: {classes}")
            environment = environments.pop()
            title = dict(attributes).get("title")
            # Titles are plain text. Pandoc supplies the necessary TeX escaping.
            title_tex = run(["pandoc", "-f", "markdown", "-t", "latex"], text=title).strip() if title else ""
            opening = "\\begin{" + environment + "}"
            if title_tex:
                opening += "[{" + title_tex + "}]"
            if label:
                opening += r"\label{" + label + "}"
            return {"t": "RawBlock", "c": ["latex", (
                opening + "\n" + latex_fragment(ast, contents)
                + "\n\\end{" + environment + "}"
            )]}
        return value

    blocks = walk(blocks, convert)
    body = latex_fragment(ast, blocks)
    expected = Counter(re.findall(r"^:{3,}\s+\{\.([a-z]+)\b", source, re.MULTILINE))
    actual = Counter(environment for environment in re.findall(r"\\begin\{([^}]+)\}", body)
                     if environment in STATEMENT_ENVIRONMENTS)
    if expected != actual or re.search(r"^:{3,}\s*$", body, re.MULTILINE):
        raise ValueError(f"Unparsed mathematical environment in {filename}")
    return ast, body, figure_sources


def compile_tex(path):
    command = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", path.name]
    result = subprocess.run(command, cwd=path.parent, text=True, capture_output=True)
    path.with_suffix(".build.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"TeX failed: see {path.with_suffix('.build.log')}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True, help="External output directory")
    parser.add_argument("--no-compile", action="store_true", help="Assemble sources only")
    args = parser.parse_args()
    output = args.output.resolve()
    if output == PROJECT or PROJECT in output.parents:
        parser.error("Build output must be outside the source checkout")
    output.mkdir(parents=True, exist_ok=True)
    figures = output / "figures"
    figures.mkdir(exist_ok=True)
    sections = []
    figure_sources = []
    intro = None
    for prefix, filename in SECTIONS:
        ast, body, stems = assemble_section(prefix, filename)
        if intro is None:
            intro = ast
        sections.append(body)
        figure_sources.extend(stems)
    title = latex_fragment(intro, [{"t": "Plain", "c": intro["meta"]["title"]["c"]}]).strip()
    abstract = latex_fragment(intro, intro["meta"]["abstract"]["c"]).strip()
    header = (SOURCE / "tex/manuscript-preamble.tex").read_text()
    authors = (SOURCE / "tex/manuscript-authors.tex").read_text()
    manuscript = (header + "\n\\hypersetup{pdftitle={" + title + "}}\n"
                  + "\\title[Elementary expansions of LLT polynomials]{" + title + "}\n"
                  + authors + "\n\\date{}\n"
                  + "\\begin{document}\n\\begin{abstract}\n" + abstract
                  + "\n\\end{abstract}\n\\maketitle\n"
                  + "\n".join(sections)
                  + "\n\\bibliographystyle{alpha}\n\\bibliography{references}\n"
                  + "\\end{document}\n")
    labels = re.findall(r"\\label\{([^}]+)\}", manuscript)
    if len(labels) != len(set(labels)):
        raise ValueError("Duplicate manuscript label")
    references = set(re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", manuscript))
    if references - set(labels):
        raise ValueError(f"Missing manuscript labels: {sorted(references - set(labels))}")
    (output / "manuscript.tex").write_text(manuscript)
    inputs = [SOURCE / name for _, name in SECTIONS]
    inputs += [SOURCE / "references.bib", SOURCE / "tex/manuscript-preamble.tex",
               SOURCE / "tex/manuscript-authors.tex", SOURCE / "tex/llt-diagrams.sty",
               Path(__file__).resolve()]
    shutil.copy2(SOURCE / "references.bib", output)
    shutil.copy2(SOURCE / "tex/llt-diagrams.sty", figures)
    for stem in figure_sources:
        path = SOURCE / "tex" / (stem + ".tex")
        inputs.append(path)
        shutil.copy2(path, figures)
        if not args.no_compile:
            print(f"Figure: {stem}", flush=True)
            compile_tex(figures / path.name)
    manifest = {str(path.relative_to(SOURCE)): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in inputs}
    (output / "source-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if not args.no_compile:
        print("Manuscript", flush=True)
        compile_tex(output / "manuscript.tex")
        log = (output / "manuscript.log").read_text()
        if re.search(r"Overfull|LaTeX Warning:.*undefined", log):
            raise RuntimeError(f"Unresolved layout/reference issue: {output / 'manuscript.log'}")
        with zipfile.ZipFile(output / "manuscript-source.zip", "w", zipfile.ZIP_DEFLATED) as bundle:
            for name in ["manuscript.tex", "references.bib", "source-manifest.json"]:
                bundle.write(output / name, name)
            for stem in figure_sources:
                for suffix in [".tex", ".pdf"]:
                    name = stem + suffix
                    bundle.write(figures / name, "figures/" + name)
            bundle.write(figures / "llt-diagrams.sty", "figures/llt-diagrams.sty")
            for path in inputs:
                bundle.write(path, "canonical/" + str(path.relative_to(SOURCE)))
            bundle.writestr("README.txt", (
                "Compile manuscript.tex with latexmk -pdf manuscript.tex.\n"
                "All included figures are vector PDFs with editable TeX sources.\n"
                "The canonical Markdown sections and assembler are in canonical/.\n"
                "Regenerate with Python 3, Pandoc and TeX Live:\n"
                "python3 canonical/build_manuscript.py --output /external/output/path\n"
            ))
    print(output / ("manuscript.tex" if args.no_compile else "manuscript.pdf"))


if __name__ == "__main__":
    main()
