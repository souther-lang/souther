package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comment survives formatting at every boundary between two of a fixture's tokens.
 *
 * <p>Not at every position the grammar admits one, which is what this used to claim: what is
 * quantified over is the boundaries of the fixtures below, and a form no fixture is written in is a
 * form nothing here asks about. A qualified name in a {@code constructs} clause was such a form, and
 * the formatter refused it.
 *
 * <p>The places are found rather than listed. {@link CommentSurvivalTest} lists them, and a list is
 * the formatter's own idea of where a comment goes written down a second time: the places it omits
 * are exactly the places the formatter drops a comment, which is how an {@code invariant} clause and
 * the end of a member list went unnoticed. So a probe comment is written into every boundary between
 * two of a fixture's tokens, and required back from every variant that still parses.
 *
 * <p>Required back as a comment, not as text. Counting {@code // probe} in the output says it
 * survived when it was written into another comment's line, where it is no longer a comment and a
 * reader has lost it. So the output is parsed and its {@code LINE_COMMENT} tokens compared against
 * the input's.
 *
 * <p>Boundaries, not existing whitespace: a comment goes between two tokens whether or not anything
 * was written between them already, so {@code f(a)} admits one after its {@code (} as much as
 * between two statements. And several fixtures, because a construct's empty form takes a different
 * path through the formatter than its occupied one — an {@code exposing} clause with no entries has
 * no member to hang a comment on and is exactly where one went missing.
 */
class AProbeSurvivesAtEveryTokenBoundaryTest {

    private static final String PROBE = "// probe";

    /** One of everything a module can be written with. Kept in canonical form, so a variant differs
     * from it only by the probe. */
    private static final String WHOLE_MODULE = """
            module m exposing ( A, B, S, run, value )
            import other.mod ( Thing )

            data A =
                { id: Int
                , name: String
                }

            data B =
                { ...A
                , extra: Int
                }

            data Small = Int
                invariant value > 0

            data One

            data Two

            data S = One | Two

            behavior run : (a: A, n: Int) -> B | Small
                constructs B, other.mod.Thing
                depends on helper

            let helper (n: Int) = n

            let run (a, n, helper) = {
                let doubled = helper(n)
                let list = [1, 2, doubled]
                guard doubled > 0 else Small(1)
                match value(a) with
                    | One -> B { ...a, extra = doubled }
                    | Two -> B { ...a, extra = 0 }
            }

            let value (a: A) = if a.id > 0 then One else Two

            example helper
                | "it doubles" : (2) -> 2

            fake helper
                | (2) -> 4
            """;

    /** The forms the whole module has no room for: an attempt's departures, a pipeline's stages, an
     * example's bindings, a comprehension, and the empty forms of the bracketed constructs. */
    private static final String THE_OTHER_FORMS = """
            module m exposing (  )
            import other.mod

            data Amount = Int
                invariant value > 0

            data In =
                { n: Int
                }

            data Out =
                { n: Int
                }

            behavior make : (n: Int) -> Out | Amount
                constructs Out, Amount

            behavior through : (i: In) -> Out
                constructs Out

            behavior piped = through >-> through -> Out

            let empty = Out {}

            let counted = 1 + 2 + 3

            let piped = 1 |> plus |> plus

            let plus (x: Int) = x + 1

            data Held =
                { xs: List<Int>
                , pair: (Int, Int)
                }

            let make (n) = {
                guard Amount(n) as a else
                    | value -> Amount(1)
                let evens = [x | x > 0]
                Out { n = a.value }
            }

            let through (i) = if i.n > 0 then Out { n = 1 } else Out { n = 0 }

            example make
                | "it makes" : (2) with n = 2 -> Out { n = 2 }
            """;

    /** A fixture that does not parse contributes nothing: every variant of it is skipped, and the
     * sweep reports a clean run over the ones that are left. So the fixtures are checked, and so is
     * how many variants each of them actually contributed. */
    @Test
    void theFixturesParseAndAreInCanonicalForm() {
        for (String fixture : List.of(WHOLE_MODULE, THE_OTHER_FORMS)) {
            assertEquals(List.of(), CstParser.parse(fixture).errors(), "a fixture does not parse");
            assertEquals(fixture, Formatter.format(fixture), "a fixture is not in canonical form");
        }
    }

    @Test
    void aProbeOnALineOfItsOwnComesBackExactlyOnce() {
        sweep(true);
    }

    @Test
    void aProbeAtTheEndOfALineComesBackExactlyOnce() {
        sweep(false);
    }

    private static void sweep(boolean onItsOwnLine) {
        List<String> lost = new ArrayList<>();
        List<String> rewritten = new ArrayList<>();
        List<String> refused = new ArrayList<>();
        int checked = 0;
        java.util.Map<Integer, Integer> contributed = new java.util.LinkedHashMap<>();
        for (String fixture : List.of(WHOLE_MODULE, THE_OTHER_FORMS)) {
            List<String> expected = commentsOf(fixture);
            int before = checked;
            for (String variant : variants(fixture, onItsOwnLine)) {
                if (!CstParser.parse(variant).errors().isEmpty()) {
                    continue;   // the probe made this one unparseable; nothing to ask of it
                }
                checked++;
                List<String> want = new ArrayList<>(expected);
                want.add(PROBE);
                want.sort(null);
                String formatted;
                try {
                    formatted = Formatter.format(variant);
                } catch (RuntimeException e) {
                    refused.add(context(variant) + "  " + e.getMessage());
                    continue;
                }
                if (!CstParser.parse(formatted).errors().isEmpty()) {
                    rewritten.add(context(variant) + "  did not parse: "
                            + CstParser.parse(formatted).errors());
                    continue;
                }
                List<String> got = commentsOf(formatted);
                got.sort(null);
                if (!want.equals(got)) {
                    lost.add(context(variant) + "  gave " + got);
                }
                if (!code(variant).equals(code(formatted))) {
                    rewritten.add(context(variant) + "  gave " + code(formatted));
                }
            }
            contributed.put(contributed.size(), checked - before);
        }

        for (var e : contributed.entrySet()) {
            assertTrue(e.getValue() > 50,
                    "a fixture contributed only " + e.getValue() + " variants; it is not being swept");
        }
        assertTrue(checked > 150, "only " + checked + " variants parsed; the sweep found nothing");
        assertTrue(lost.isEmpty() && rewritten.isEmpty() && refused.isEmpty(),
                "of " + checked + " swept, " + lost.size() + " came back with the comments changed,"
                        + " " + rewritten.size() + " with the code changed and " + refused.size()
                        + " were refused.\ncomments changed after:\n" + String.join("\n", lost)
                        + "\ncode changed after:\n" + String.join("\n", rewritten)
                        + "\nrefused after:\n" + String.join("\n", refused));
    }

    /** {@code source} with a probe comment written into one boundary between two of its tokens, one
     * variant per boundary. A comment is written either on a line of its own or at the end of the
     * line it is inside, and the two are separate questions, so a sweep asks one of them. */
    private static List<String> variants(String source, boolean onItsOwnLine) {
        List<String> out = new ArrayList<>();
        for (int at : boundaries(source)) {
            String written = onItsOwnLine ? "\n" + PROBE + "\n" : " " + PROBE + "\n";
            out.add(source.substring(0, at) + written + source.substring(at));
        }
        return out;
    }

    /** Where a comment can go: after each token that is not trivia. Trivia is skipped when the
     * parser looks for its next token, so a boundary exists whether or not anything was written at
     * it. */
    private static List<Integer> boundaries(String source) {
        List<Integer> out = new ArrayList<>();
        for (SyntaxToken t : tokens(CstParser.parse(source).root())) {
            if (!t.isTrivia() && t.kind() != SyntaxKind.EOF && !out.contains(t.end())) {
                out.add(t.end());
            }
        }
        return out;
    }

    /**
     * What {@code source} says, with the trivia dropped. Formatting rewrites the layout and nothing
     * else, so this is the same before and after — and a comment that swallowed the code after it
     * shows up here rather than in the comments, which come back one for one either way.
     */
    private static List<String> code(String source) {
        List<String> out = new ArrayList<>();
        for (SyntaxToken t : tokens(CstParser.parse(source).root())) {
            if (!t.isTrivia()) {
                out.add(t.kind() + " " + t.text());
            }
        }
        return out;
    }

    /** The comments {@code source} holds, read back as comments rather than as text. */
    private static List<String> commentsOf(String source) {
        List<String> out = new ArrayList<>();
        for (SyntaxToken t : tokens(CstParser.parse(source).root())) {
            if (t.kind() == SyntaxKind.LINE_COMMENT) {
                out.add(t.text().stripTrailing());
            }
        }
        return out;
    }

    private static List<SyntaxToken> tokens(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                out.addAll(tokens(c));
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
        return out;
    }

    /** The words the probe was written after, so a failure names the boundary rather than an offset. */
    private static String context(String variant) {
        int at = variant.indexOf(PROBE);
        int from = Math.max(0, at - 40);
        return "    ..." + variant.substring(from, at).replace("\n", "\\n") + "[probe]";
    }
}
