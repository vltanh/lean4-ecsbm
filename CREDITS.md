# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, the paper's first author, who asked for the
  formalization of its published version.
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`, Anthropic), in Claude Code 2.1.291 (VS
  Code extension), in one session with sub-agents. There was no earlier draft.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill,
  version 2.2.0 (commit `d82a98e1237e5b864bb76185b1ebb5548092a184`).
- **Review:** no person has reviewed the proofs yet. Separate agents reviewed the statements and
  the Challenge against the paper (twice), compared the formal proofs with the paper's, searched
  the literature, and checked the findings of the report against the paper.

## First formalization (7 October 2026)

How it was made:

- **The paper.** The main session found the paper's versions: the published version, which the
  request linked, and the earlier arXiv version, with its TeX source. It formalized the published
  version, from the publisher's HTML (whose mathematics is TeX) and PDF, and wrote an inventory of
  its definitions, results, constants and suspected slips.
- **The statements.** The main session set up the project on Lean and Mathlib `v4.35.0-rc4` and
  wrote every definition and statement with `sorry`, with the Challenge. A sub-agent reviewed them
  against the published text; the main session applied its findings, and the same sub-agent
  reviewed the changes. Then the baseline was committed.
- **The proofs.** The main session drafted every proof in a scratch file while the review ran, and
  moved them into the library after the baseline. No sub-agent wrote a proof, and no statement
  changed after the baseline. The paper cites no result in its proofs, so there was no second
  stage.
- **The checks.** The main session wrote the Solution and ran Comparator, the axiom audit and the
  route check. A sub-agent compared the formal proofs with the paper's and checked the slips found;
  it found no departure.
- **The audit.** A sub-agent searched the literature; the main session wrote [`REPORT.md`](REPORT.md) and
  [`README.md`](README.md); another sub-agent checked every finding against the paper and every summary of
  another work against its source. The main session also checked two observations for Section 11
  numerically and one in Lean.
- **Packaging.** The main session wrote the Palomar files and ran Palomar's local checks; at the
  author's choice, the project is not submitted to Palomar.

Figures, from 7 October 2026, 17:48 CDT, to the commit that completes [`REPORT.md`](REPORT.md)
(`95cef720`, 19:21 CDT), taken from the session's transcripts with the skill's
`session_stats.py`:

- **Elapsed time:** 1.55 hours (1 hour 33 minutes).
- **Sub-agents:** 4 (the statement review, resumed once for a second pass; the proof comparison;
  the literature search; the audit verification), at most 2 running at once, for 1.3 hours of
  working time in all.
- **Tool calls and tokens:** the sub-agents made 297 tool calls, with 0.42 million output tokens,
  1.08 million input tokens and 46 million cache reads; the main session made 208 tool calls, with
  0.43 million output tokens, 0.72 million input tokens and 90 million cache reads.
- **Model calls:** 473, all to Claude Opus 5.5 (200 by the main session, 273 by the sub-agents).

The elapsed time includes the builds and the downloads, which the transcripts do not separate
from the rest. The figures leave out the work after the report: the credits, and the final checks
of the packaging.
