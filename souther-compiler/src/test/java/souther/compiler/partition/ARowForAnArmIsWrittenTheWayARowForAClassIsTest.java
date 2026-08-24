package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row offered for an arm, written against a value the module states.
 *
 * <p>A row for a class is composed against a value the model already states, so what differs between
 * it and what is written in the file is the class and the class alone. A row for an arm was composed
 * from the classes, and every position the way into the arm left free held whatever the search
 * happened to name there. A reader was handed both in one block: the first says what it is about by
 * differing from a value they recognise, and the second by being a row they have to read whole
 * (issue #1034).
 *
 * <p>They are one search over two demands. A class asks for one class at one position; a way into an
 * arm asks for a class apiece at the positions it settles; and what is nearest to what the model
 * states is the same question either way. What differed was only that the values the model states
 * never reached the second of them.
 *
 * <p>The arm here is behind a decision over two positions, so no row composed for a class of either
 * of them arrives at it — which is what leaves the arm owed a row of its own for this to be about.
 */
class ARowForAnArmIsWrittenTheWayARowForAClassIsTest {

    private static final String CORRELATED = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Request = { lo: Amount, hi: Amount }
                invariant lo.value <= hi.value

            data Flag = Off | On

            data Accepted = { at: String }

            let mid = Request { lo = Amount(60), hi = Amount(70) }

            behavior submit : (request: Request, a: Flag, b: Flag) -> Accepted
                constructs Accepted

            let one (f: Flag): Int =
                match f with
                    | Off -> 0
                    | On -> 1

            let submit (request, a, b) = {
                guard request.lo.value <= 50 else Accepted { at = "wide" }
                guard one(a) + one(b) >= 2 else Accepted { at = "partial" }
                Accepted { at = "both" }
            }

            example submit
                | "a wide one" : (mid, Off, Off) -> Accepted { at = "wide" }
            """;

    /**
     * The row offered for an arm names the value the model states, with the positions the arm needs
     * moved and nothing else.
     *
     * <p>{@code request} takes no part in the decision this arm is behind, so the row says what it
     * has always said about it: {@code mid}, with the one field the way in needs. Composed from the
     * classes, both of its fields were written out at whatever the search named, and a reader had to
     * work out which of the differences the arm turned on.
     */
    @Test
    void aRowOfferedForAnArmNamesTheValueTheModelStates() {
        List<String> rows = rowsForArmsAlone();

        assertFalse(rows.isEmpty(), "this model leaves an arm no class's row arrives at");
        assertEquals(List.of("Request { ...mid, lo = Amount(0) }, On, Off"), rows);
    }

    /** The rows offered for an arm and for nothing else, which are the ones the class search never
     *  touched. */
    private static List<String> rowsForArmsAlone() {
        Compilation compilation = Compilation.ofSource(CORRELATED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        Adequacy.Filling filling = all.get("submit");
        assertNotNull(filling, "the behavior under test is generated for");
        return filling.composed().rows().stream()
                .filter(row -> row.purposes().stream()
                        .noneMatch(Generator.Purpose.ForAClass.class::isInstance))
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }
}
