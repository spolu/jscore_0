/**
 * Annotation parser — extracts @requires, @invariant, @ensures from comments.
 * Hand-written recursive descent parser for the property grammar.
 */

export interface RequiresAnnotation {
  kind: "requires";
  prop: string;
}

export interface InvariantAnnotation {
  kind: "invariant";
  tag: string;
  prop: string;
}

export interface EnsuresAnnotation {
  kind: "ensures";
  binding: string;
  pred: string;
}

export type Annotation = RequiresAnnotation | InvariantAnnotation | EnsuresAnnotation;

/**
 * Parse annotations from a list of comment texts.
 * Comments may be single-line (//) or multi-line blocks.
 * Multi-line annotations use continuation: lines starting with // that follow
 * an annotation line and are indented further are continuations.
 */
export function parseAnnotations(commentTexts: string[]): Annotation[] {
  const annotations: Annotation[] = [];

  for (const text of commentTexts) {
    const lines = text.split("\n").map((l) => l.trim());

    let i = 0;
    while (i < lines.length) {
      let line = lines[i];
      // Strip leading comment markers
      line = line.replace(/^\/\/\s*/, "").replace(/^\*\s*/, "").trim();

      if (line.startsWith("@requires ")) {
        const prop = collectContinuation(lines, i, "@requires ".length);
        i = prop.nextIndex;
        annotations.push({ kind: "requires", prop: prop.text });
      } else if (line.startsWith("@invariant ")) {
        const rest = collectContinuation(lines, i, "@invariant ".length);
        i = rest.nextIndex;
        const colonIdx = rest.text.indexOf(":");
        if (colonIdx >= 0) {
          annotations.push({
            kind: "invariant",
            tag: rest.text.slice(0, colonIdx).trim(),
            prop: rest.text.slice(colonIdx + 1).trim(),
          });
        }
      } else if (line.startsWith("@ensures ")) {
        const rest = collectContinuation(lines, i, "@ensures ".length);
        i = rest.nextIndex;
        const dotIdx = rest.text.indexOf(".");
        if (dotIdx >= 0) {
          annotations.push({
            kind: "ensures",
            binding: rest.text.slice(0, dotIdx).trim(),
            pred: rest.text.slice(dotIdx + 1).trim(),
          });
        }
      } else {
        i++;
      }
    }
  }

  return annotations;
}

function collectContinuation(
  lines: string[],
  startIdx: number,
  prefixLen: number
): { text: string; nextIndex: number } {
  let line = lines[startIdx];
  line = line.replace(/^\/\/\s*/, "").replace(/^\*\s*/, "").trim();
  let text = line.slice(prefixLen).trim();
  let i = startIdx + 1;

  // Collect continuation lines (indented lines following the annotation)
  while (i < lines.length) {
    let next = lines[i];
    next = next.replace(/^\/\/\s*/, "").replace(/^\*\s*/, "").trim();
    // Continuation if it doesn't start with @ and isn't empty
    if (next && !next.startsWith("@")) {
      text += " " + next;
      i++;
    } else {
      break;
    }
  }

  return { text, nextIndex: i };
}

/**
 * Extract annotations from comment text preceding a function declaration.
 */
export function extractFunctionAnnotations(
  leadingComments: string[]
): { requires: RequiresAnnotation[]; invariants: InvariantAnnotation[] } {
  const all = parseAnnotations(leadingComments);
  return {
    requires: all.filter((a): a is RequiresAnnotation => a.kind === "requires"),
    invariants: all.filter(
      (a): a is InvariantAnnotation => a.kind === "invariant"
    ),
  };
}

/**
 * Extract @ensures annotations from inline comments after a statement.
 */
export function extractEnsuresAnnotations(
  comments: string[]
): EnsuresAnnotation[] {
  const all = parseAnnotations(comments);
  return all.filter((a): a is EnsuresAnnotation => a.kind === "ensures");
}
