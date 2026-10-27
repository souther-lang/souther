package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.report.GeneratedRows;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class an equality of two strings parts a position into has a row, and the row is one the
 * equality comes out the way the class says on.
 *
 * <p>That the classes are read is not that they can be written down: a class no row can be built
 * for is a division the measure owes a row at and cannot pay. So the rows offered are written out
 * and run, as a person who pastes them would run them. A row is refused before the body is applied
 * where it breaks a rule of either position, and answers where it does not.
 */
class ARowOfferedForAnEqualityOfTwoStringsIsOneTheEqualityCanComeOutThatWayOnTest {

    private static String model(String first, String second) {
        return """
                module demo

                data L = String
                    invariant String.matches("%s", value)
                data M = String
                    invariant String.matches("%s", value)

                behavior same : (a: L, b: M) -> Bool
                let same (a, b) = a.value == b.value
                """.formatted(first, second);
    }

    /** What running each row offered for {@code model} came to. */
    private static List<RowOutcome> ran(String model) {
        Compilation compilation = Compilation.ofSources(List.of(model), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        StringBuilder offered = new StringBuilder();
        for (String module : compilation.modules()) {
            offered.append(GeneratedRows.of(
                    Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule(module)),
                    Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                    compilation.db()).text());
        }
        Compilation pasted = Compilation.ofSources(List.of(model + "\n" + offered),
                ModulePath.EMPTY);
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : pasted.modules()) {
            for (SourceId id : pasted.exampleSourcesOf(module)) {
                Output.Examples.Of result = pasted.db()
                        .ask(Output.Examples.asked(pasted.db(), module, id)).value();
                if (result != null) {
                    rows.addAll(result.rows());
                }
            }
        }
        return rows;
    }

    private static boolean equalWas(RowOutcome row) {
        AnswerObservation.Answered answered =
                assertInstanceOf(AnswerObservation.Answered.class, row.answer());
        return assertInstanceOf(ObservedValue.Bool.class, answered.value()).value();
    }

    private static String textAt(RowOutcome row, int input) {
        ObservedValue.Constructed named =
                assertInstanceOf(ObservedValue.Constructed.class, row.inputs().get(input));
        return assertInstanceOf(ObservedValue.Text.class, named.field("value")).value();
    }

    private static void everyRowIsAnswered(List<RowOutcome> rows) {
        assertFalse(rows.isEmpty(), "the classes have rows offered");
        for (RowOutcome row : rows) {
            assertEquals(Stage.ANSWERED, row.stage(),
                    "a row offered meets the rule of both positions: " + row);
        }
    }

    @Test
    void whereTheOtherSideHoldsMoreTheStringsOnlyItHoldsHaveARowThatIsNotEqual() {
        List<RowOutcome> rows = ran(model("[a-z]+", "[a-z0-9]+"));

        everyRowIsAnswered(rows);
        List<RowOutcome> withADigit = rows.stream()
                .filter(row -> textAt(row, 1).matches(".*[0-9].*")).toList();
        assertFalse(withADigit.isEmpty(), "the strings no letters-only value is have a row");
        for (RowOutcome row : withADigit) {
            assertFalse(equalWas(row), "no value of the first position holds a digit: " + row);
        }
        assertTrue(rows.stream().anyMatch(row -> textAt(row, 1).matches("[a-z]+")),
                "and the strings both hold have one");
    }

    @Test
    void whereTwoLanguagesOverlapEachPositionHasARowOnEitherSideOfWhatTheOtherHolds() {
        List<RowOutcome> rows = ran(model("[a-c]+", "[b-d]+"));

        everyRowIsAnswered(rows);
        assertTrue(rows.stream().anyMatch(row -> textAt(row, 0).matches("[bc]+")),
                "a string of the first that the second holds");
        assertTrue(rows.stream().anyMatch(row -> textAt(row, 0).contains("a")),
                "a string only the first holds");
        assertTrue(rows.stream().anyMatch(row -> textAt(row, 1).matches("[bc]+")),
                "a string of the second that the first holds");
        assertTrue(rows.stream().anyMatch(row -> textAt(row, 1).contains("d")),
                "a string only the second holds");
        for (RowOutcome row : rows) {
            if (textAt(row, 0).contains("a") || textAt(row, 1).contains("d")) {
                assertFalse(equalWas(row),
                        "a string only one of them holds is equal to none of the other's: " + row);
            }
        }
    }

    @Test
    void whereTwoLanguagesShareNothingNoRowIsOfferedEqual() {
        List<RowOutcome> rows = ran(model("[a-c]+", "[x-z]+"));

        everyRowIsAnswered(rows);
        for (RowOutcome row : rows) {
            assertFalse(equalWas(row), "no string is held by both: " + row);
        }
    }
}
