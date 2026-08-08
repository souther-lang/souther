package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A gate that says a file is not formatted has said what is wrong with it. This is what says why:
 * the rule the source departs from, named as its row is written.
 *
 * <p>It is one call per adjacency. The rule reads the kind on each side and the construct joining
 * them, and all three are in the source's own tree, so a deviation is that answer disagreeing with
 * what is written. While the answer was the by-product of whichever literal a construct spelled,
 * attributing a difference meant finding that literal — which is the part of issue #444's estimate
 * that issue #476 was about removing.
 */
class ADeviationNamesTheRuleItDepartsFromTest {

    private static List<SpacingDeviation.Deviation> of(String source) {
        return SpacingDeviation.of(CstParser.parse(source).root(), source);
    }

    @Test
    void eachOneNamesTheRuleAndBothAnswers() {
        List<SpacingDeviation.Deviation> found = of("""
                module m

                let f (a: Int) : Int = g( a , 1 )
                """);
        assertEquals(List.of(
                "RPAREN COLON under FN_DEF: [ ] for []",
                "LPAREN IDENT under ARG_LIST: [ ] for []",
                "IDENT COMMA under ARG_LIST: [ ] for []",
                "INT_LIT RPAREN under ARG_LIST: [ ] for []"),
                found.stream()
                        .map(d -> d.rule() + ": [" + d.written() + "] for [" + d.canonical() + "]")
                        .toList());
    }

    /** And says where, so that the reader is not left to find it in the diff. */
    @Test
    void andWhereItIs() {
        String source = "module m\n\nlet f (a: Int) : Int = a\n";
        List<SpacingDeviation.Deviation> found = of(source);
        assertEquals(1, found.size(), found.toString());
        assertEquals(source.indexOf(") :") + 1, found.get(0).offset());
    }

    /**
     * The same pair written two ways under two constructs is two rules, and a source is answered by
     * the one that holds where it wrote it: a list of names is written open and everything else
     * bracketed is not, so `exposing (f)` departs and `g(a)` does not.
     */
    @Test
    void theRuleNamedIsTheOneThatHoldsWhereItWasWritten() {
        assertEquals(List.of("LPAREN IDENT under EXPOSING_CLAUSE: [] for [ ]",
                        "IDENT RPAREN under EXPOSING_CLAUSE: [] for [ ]"),
                of("module m exposing (f)\n").stream()
                        .map(d -> d.rule() + ": [" + d.written() + "] for [" + d.canonical() + "]")
                        .toList());
        assertEquals(List.of(), of("""
                module m

                let f (a: Int): Int = g(a)
                """));
    }

    /** A line broken where the canonical form would not break it is a different rule's, and this
     * has nothing to say about it — what two tokens have between them is what it reads, and there
     * are no two tokens on a line here that disagree with it. */
    @Test
    void aLineBrokenElsewhereIsADifferentRulesBusiness() {
        assertEquals(List.of(), of("""
                module m

                let f (a: Int): Int =
                    a
                """));
    }

    /** And a source already in its canonical form departs from nothing. */
    @Test
    void aCanonicalSourceDepartsFromNothing() {
        String canonical = Formatter.format("""
                module m exposing ( f )

                let f (a: Int, b: Decimal): Int = g(a, 1, "x", true)
                """);
        assertTrue(of(canonical).isEmpty(), of(canonical).toString());
    }
}
