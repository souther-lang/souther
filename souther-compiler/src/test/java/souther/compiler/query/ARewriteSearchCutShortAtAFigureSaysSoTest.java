package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A search for a row a rewrite answers differently on, cut short where composing the rows it
 * looked through stopped at a figure of its own, says so: what a wider run would raise is what a
 * reader of an undecided rewrite acts on, and a search cut short is not one that composed nothing.
 *
 * <p>The body answers whether a value holds more than this compiler composes for one, so every row
 * small enough to compose answers alike under the rewrite and the walk over how many it holds stops
 * at its figure.
 */
class ARewriteSearchCutShortAtAFigureSaysSoTest {

    @Test
    void aListLongerThanAnyComposedIsAFigureReached() {
        assertCutShortAtAFigure("""
                module example.many

                data Ok = { many: Bool }

                behavior f : (xs: List<Int>) -> Ok
                    constructs Ok

                let f (xs) = Ok { many = List.length(xs) >= 1000 }

                example f
                    | ([]) -> Ok { many = false }
                    | ([1, 2]) -> Ok { many = false }
                """);
    }

    @Test
    void aStringLongerThanAnyComposedIsAFigureReached() {
        assertCutShortAtAFigure("""
                module example.long

                data Ok = { long: Bool }

                behavior f : (s: String) -> Ok
                    constructs Ok

                let f (s) = Ok { long = String.length(s) >= 5000 }

                example f
                    | ("") -> Ok { long = false }
                    | ("ab") -> Ok { long = false }
                """);
    }

    private static void assertCutShortAtAFigure(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code()).toList(),
                "the model under test compiles");
        ReplacementEvidence its = compilation.db()
                .ask(new Replacements.Measured(compilation.modules().get(0))).value().get("f");
        List<ReplacementEvidence.Rewrite> rewrites = its.measured().made()
                .orElseThrow(() -> new AssertionError("the rewrites were measured: " + its))
                .rewrites();
        assertEquals(1, rewrites.size(), "the body answering what every row answers: " + rewrites);
        ReplacementEvidence.Undecided open = assertInstanceOf(ReplacementEvidence.Undecided.class,
                rewrites.getFirst().outcome(), "no row composed tells it apart: " + rewrites);
        List<ReplacementEvidence.Undecided.Why> why = open.why().reasons().written();
        assertTrue(why.contains(ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED),
                "and composing stopped at a figure of its own on the way: " + why);
    }
}
