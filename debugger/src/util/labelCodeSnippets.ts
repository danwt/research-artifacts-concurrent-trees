
import _ from "lodash";

// const src = tlaCode.content;
const src = "";

function extractPluscalOnly(src: string) {
  const PREF = "\\* BEGIN TRANSLATION";
  const SUFF = "\\* END TRANSLATION";
  const lines = _.split(src, "\n");
  const isPref = lines.map((it) => it.startsWith(PREF));
  const isSuff = lines.map((it) => it.startsWith(SUFF));
  const prefIx = isPref.indexOf(true);
  const suffIx = isSuff.indexOf(true);
  const beforePref = lines.slice(0, prefIx + 1);
  const afterSuff = lines.slice(suffIx);
  const ret = beforePref.concat(afterSuff);
  return ret;
}

const pluscalLines: string[] = extractPluscalOnly(src);

/**
 * Note: assume all labels are at the beginning of lines
 */
function createLabelsToLineNumberMap(lines: string[]) {
  let ret = new Map<string, number>();
  lines.forEach((it, i) => {
    let words = it.split(" ");
    if (0 < words.length) {
      let trimmed = _.trimEnd(words[0]);
      if (trimmed.endsWith(":")) {
        ret.set(trimmed.slice(0, -1), i);
      }
      if (trimmed.endsWith(":+")) {
        ret.set(trimmed.slice(0, -2), i);
      }
    }
  });
  return ret;
}

const labelsToLineNumber: Map<string, number> = createLabelsToLineNumberMap(
  pluscalLines
);

function labelToLineIx(label: string): number | undefined {
  return labelsToLineNumber.get(label);
}

const LINES_BEFORE = 19;
const NUM_LINES = 100; // Intentionally generous to allow scroll down

function snippetForLabel(label: string): string {
  const labelIx = labelToLineIx(label);

  if (labelIx === undefined) {
    console.log("labelz not found");
    return "";
  }

  const startIx = Math.max(0, labelIx - LINES_BEFORE);
  const endIx = startIx + NUM_LINES;
  const lines = pluscalLines.slice(startIx, endIx);
  const ret = _.join(lines, "\n");
  return ret;
}

const defaultSnippet = src;

export { snippetForLabel, defaultSnippet };
