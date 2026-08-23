package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which values a generated row may be written against.
 *
 * <p>A row written against a value the model states reads as that value with one class moved, which
 * is what makes it readable at all. What the model states is a value of a type. That two of them go
 * together is a further thing, and a module declaring one after the other states nothing of the
 * kind.
 *
 * <p>So the tuples an origin can be are the ones somebody wrote: a row of the author's naming a
 * value at each position is a set they reached for together. Assembled here instead — the first
 * value of each type as one origin, the second of each as another — the only thing available to
 * assemble by is the order the file declares them in, and swapping two unrelated declarations moves
 * the value every generated row of the behavior is written against.
 */
class AnOriginIsATupleTheModelStatesAndNotOneAssembledHereTest {

    /** Two positions of one type, and two values of it. Nothing says which goes with which. */
    private static final String TWO_OF_A_KIND = """
            module example.span

            data Amount = Int
                invariant value >= 0

            data Bound = { at: Amount }

            data Verdict = { at: String }

            let low = Bound { at = Amount(10) }

            let high = Bound { at = Amount(90) }

            behavior between : (from: Bound, to: Bound) -> Verdict
                constructs Verdict

            let between (from, to) = {
                guard from.at.value <= 50 else Verdict { at = "late" }
                guard to.at.value <= 50 else Verdict { at = "wide" }
                Verdict { at = "now" }
            }
            """;

    /**
     * No row is written against two stated values at once.
     *
     * <p>The diagonal is what this is about. Taken as the n-th value of each position's type, the
     * origins were {@code (low, low)} and {@code (high, high)} — never {@code (low, high)} — off a
     * pairing nothing in the model draws, and a reader who swapped the two {@code let}s got
     * different rows for a change that said nothing about either.
     */
    @Test
    void noRowIsWrittenAgainstAPairTheFileMerelyDeclaresInOrder() {
        List<List<String>> rows = inputsOf(TWO_OF_A_KIND);
        assertFalse(rows.isEmpty(), "the behavior is offered rows: " + rows);

        for (List<String> row : rows) {
            // Counted per position and not per name. The diagonal pairs the n-th value of each
            // type, so both positions of a two-parameter behavior of one type are written against
            // the same `let` — a pair spelt with one name twice, which a count of distinct names
            // reads as one value.
            assertEquals(List.of(), row.stream()
                            .filter(input -> input.contains("low") || input.contains("high"))
                            .skip(1).toList(),
                    "a row is written against one stated value at most, the positions it says "
                            + "nothing about composed from their classes: " + row);
        }
    }

    // That the second stated value is an origin at all — reached where the first cannot be
    // repaired into the class — is what `aSecondValueOfOneTypeIsAnotherOriginRatherThanNone`
    // holds. Here the first builds, so the walk stops at it and never needs the second, which is
    // the ordering working rather than the second value being unused.

    /**
     * A row for a class is written against a value of the position it is about.
     *
     * <p>An origin that names some other position is one this row can still be written against, and
     * it is not that value with one field moved — the position the row is about is composed from
     * its classes like any other. So it comes after every origin that grounds that position, and
     * measuring it in the same order put it first: what an origin says nothing about is filled from
     * the classes before the distance is taken, so the filling sits at distance zero and the
     * ungrounded origin arrived as a nearest one.
     */
    @Test
    void aRowForAClassIsWrittenAgainstAValueOfThePositionItIsAbout() {
        Map<AxisId, List<String>> byClass = generatedFor(TWO_OF_A_KIND);
        List<String> row = null;
        for (Map.Entry<AxisId, List<String>> each : byClass.entrySet()) {
            if (each.getKey().term().startsWith("to")) {
                row = each.getValue();
                break;
            }
        }
        assertNotNull(row, "a class of `to` is offered a row: " + byClass);

        assertEquals(2, row.size(), "the behavior takes two positions: " + row);
        assertTrue(row.get(1).contains("low") || row.get(1).contains("high"),
                "and the row is written against a value the model states of `to`, not one it "
                        + "states of `from`: " + row);
    }

    /** One row per class of a position, by the position and class it was composed for. */
    private static Map<AxisId, List<String>> generatedFor(String source) {
        Map<AxisId, List<String>> out = new java.util.LinkedHashMap<>();
        for (Generator.GeneratedRow row : rowsOf(source)) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass about) {
                    out.putIfAbsent(about.at(), row.inputs().stream()
                            .map(FixtureTemplate::text).toList());
                }
            }
        }
        return out;
    }

    /** What each offered row's inputs are written as, one entry per position. */
    private static List<List<String>> inputsOf(String source) {
        return rowsOf(source).stream()
                .map(row -> row.inputs().stream().map(FixtureTemplate::text).toList())
                .toList();
    }

    /** The rows offered for the behavior under test. */
    private static List<Generator.GeneratedRow> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all = compilation.db()
                .ask(new Adequacy.Generated(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Adequacy.Filling filling = all.get("between");
        assertNotNull(filling, "the behavior under test is generated for");
        return filling.composed().rows();
    }
}
