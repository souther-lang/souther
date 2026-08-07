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
 * A comment survives formatting wherever the grammar admits one.
 *
 * <p>The places are found rather than listed. {@link CommentSurvivalTest} lists them, and a list is
 * the formatter's own idea of where a comment goes written down a second time: the places it omits
 * are exactly the places the formatter drops a comment, which is how an {@code invariant} clause and
 * the end of a member list went unnoticed. So this walks a fixture's whitespace, writes a probe
 * comment into each gap between two tokens, and requires the probe back — once — from every variant
 * that still parses.
 *
 * <p>Only comments written on a line of their own are swept. One written at the end of a line of
 * code is a second question — which construct it belongs to, and where that construct's line ends
 * once the layout has been re-derived — and it is asked where that is decided.
 *
 * <p>What the probe is attached to is not asserted here either. That needs an expected owner, and
 * deriving one from the insertion point would be the classifier under test written twice; it is
 * asked of hand-written cases instead.
 */
class EveryCommentTheGrammarAdmitsSurvivesTest {

    private static final String PROBE = "// probe";

    /** One of everything a module can be written with, since a gap only exists where the fixture put
     * two tokens. Kept in canonical form, so a variant differs from it only by the probe. */
    private static final String FIXTURE = """
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
                constructs B
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

            data Wide =
                { alphaMeasurement: Int
                , betaMeasurement: Int
                , gammaMeasurement: Int
                , deltaMeasurement: Int
                }

            behavior widen : (
                alphaMeasurement: Int,
                betaMeasurement: Int,
                gammaMeasurement: Int,
                deltaMeasurement: Int
            ) -> Wide
                constructs Wide

            let widen (alphaMeasurement, betaMeasurement, gammaMeasurement, deltaMeasurement) =
                Wide {
                    alphaMeasurement = alphaMeasurement,
                    betaMeasurement = betaMeasurement,
                    gammaMeasurement = gammaMeasurement,
                    deltaMeasurement = deltaMeasurement
                }

            let manyNumbers =
                [1000000000, 2000000000, 3000000000, 4000000000, 5000000000, 6000000000, 7000000000]
            """;

    @Test
    void theFixtureIsInCanonicalFormAndHasGaps() {
        assertEquals(FIXTURE, Formatter.format(FIXTURE), "the fixture is not in canonical form");
        assertTrue(gaps(FIXTURE, true).size() + gaps(FIXTURE, false).size() > 100,
                "too few gaps to be a useful sweep");
    }

    @Test
    void aProbeOnALineOfItsOwnComesBackExactlyOnce() {
        sweep(gaps(FIXTURE, true));
    }

    private static void sweep(List<String> variants) {
        List<String> lost = new ArrayList<>();
        List<String> duplicated = new ArrayList<>();
        int checked = 0;
        for (String variant : variants) {
            if (!CstParser.parse(variant).errors().isEmpty()) {
                continue;   // the probe made this one unparseable; nothing to ask of it
            }
            checked++;
            int n = occurrences(Formatter.format(variant), PROBE);
            if (n == 0) {
                lost.add(context(variant));
            } else if (n > 1) {
                duplicated.add(context(variant));
            }
        }

        assertTrue(checked > 20, "only " + checked + " variants parsed; the sweep found nothing");
        assertTrue(lost.isEmpty() && duplicated.isEmpty(),
                "the probe was dropped in " + lost.size() + " gaps and written twice in "
                        + duplicated.size() + ", of " + checked + " swept.\ndropped after:\n"
                        + String.join("\n", lost) + "\nduplicated after:\n"
                        + String.join("\n", duplicated));
    }

    /**
     * {@code source} with a probe comment written into one gap between two tokens, one variant per
     * gap. The two ways a comment is written are swept separately, because they are separate
     * questions: {@code onItsOwnLine} takes the gaps that already span a line and writes the probe
     * as a line between them, and the rest take it at the end of the line they are inside.
     */
    private static List<String> gaps(String source, boolean onItsOwnLine) {
        List<String> out = new ArrayList<>();
        for (SyntaxToken w : whitespace(CstParser.parse(source).root())) {
            String text = w.text();
            int nl = text.indexOf('\n');
            if ((nl >= 0) != onItsOwnLine) {
                continue;
            }
            String replacement = nl < 0
                    ? " " + PROBE + "\n" + text
                    : text.substring(0, nl + 1) + PROBE + text.substring(nl);
            out.add(source.substring(0, w.start()) + replacement + source.substring(w.end()));
        }
        return out;
    }

    private static List<SyntaxToken> whitespace(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                out.addAll(whitespace(c));
            } else if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.WHITESPACE) {
                out.add(t);
            }
        }
        return out;
    }

    /** The words the probe was written after, so a failure names the gap rather than an offset. */
    private static String context(String variant) {
        int at = variant.indexOf(PROBE);
        int from = Math.max(0, at - 40);
        return "    ..." + variant.substring(from, at).replace("\n", "\\n") + "[probe]";
    }

    private static int occurrences(String haystack, String needle) {
        int n = 0;
        for (int i = haystack.indexOf(needle); i >= 0; i = haystack.indexOf(needle, i + needle.length())) {
            n++;
        }
        return n;
    }
}
