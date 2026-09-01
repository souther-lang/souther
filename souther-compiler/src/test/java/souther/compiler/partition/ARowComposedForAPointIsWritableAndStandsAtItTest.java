package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row this compiler composed for a point is one a model can hold, and it stands at that point.
 *
 * <p>Two claims about one row, and neither implies the other. A row that cannot be written is one an
 * author pastes and the compiler refuses; a row that can be written and stands somewhere else is one
 * the report counts against a point it does not meet. Both were live at once and for one reason: the
 * search, the writing and the reading each took the order a position is counted on from somewhere,
 * and where they took it from the same wrong place they agreed with each other and with nothing in
 * the model (#1018).
 *
 * <p><b>Which is why the compiler stands between them here.</b> A row put back into the model is
 * type-checked and constructed by machinery that has never heard of borders, so a value written on
 * an order that is not the position's is refused there whatever the reading of the border thinks. A
 * round trip that only measured the row again would be asking the reader to confirm what the writer
 * did, which is the arrangement that hid this.
 *
 * <p><b>Soundness and not completeness.</b> Nothing here asks that a point have a row. Whether the
 * search reaches an assignment moves with what a model leaves each position, and a point with none
 * is the search's answer rather than a broken promise (#949) — so every row offered is held to these
 * two claims, and a point that offers none says nothing. What must exist is asked where it can be
 * argued for: {@link ARowOfferedForABorderOverAnOperationStandsAtItTest} names one border and the
 * four points it draws.
 *
 * <p>Over every operation declared to answer a form of its arguments, which is the set that puts an
 * operation between a rule and the positions it is about. The models are the ones beside this, so an
 * operation declared later is measured here without being added here.
 */
class ARowComposedForAPointIsWritableAndStandsAtItTest {

    /**
     * The answer written beside a composed row, which is not what this is about.
     *
     * <p>A row is offered with its result left for an author to fill in, and an example line needs
     * one. Working it out would mean writing each model's rule a second time in Java, once per
     * operation declared — so one is written down and the disagreement it may cause is allowed for
     * below. What the row is being held to is that the inputs are writable and that they stand where
     * they were composed to stand, and neither of those is a question about the answer.
     */
    private static final String WHATEVER = "Ok";

    /**
     * A row whose stated answer is wrong, which is the one thing said about these rows that is not
     * being asked.
     *
     * <p>Allowed for rather than avoided. A row that ran, whose inputs were built and whose guard
     * was taken, is complete evidence about which points it stands at however the answer beside it
     * came out — the run reached the comparison to disagree at all. Any other diagnostic is a row
     * this compiler composed and this compiler will not take.
     */
    private static final String THE_ANSWER_DISAGREES = "E1905";

    /** Every row composed for a point of one of these models is one the model can hold. */
    @Test
    void everyRowComposedIsOneTheModelCanHold() {
        Map<String, List<String>> refused = new LinkedHashMap<>();
        forEachComposedRow((model, point, row) -> {
            List<String> said = otherThanTheAnswer(model + example(row));
            if (!said.isEmpty()) {
                refused.put(point + " -> " + row, said);
            }
        });

        assertEquals(Map.of(), refused,
                "a row this compiler composed is one it will read back");
    }

    /** And once it is in, the point it was composed for is met. */
    @Test
    void everyRowComposedStandsAtThePointItWasComposedFor() {
        List<String> missed = new ArrayList<>();
        forEachComposedRow((model, point, row) -> {
            if (!met(lines(model + example(row)), point)) {
                missed.add(point + " -> " + row);
            }
        });

        assertEquals(List.of(), missed,
                "a row composed for a point stands at that point once it is in the model");
    }

    /** What each of the two claims is applied to: a model, a point of it, and the row composed
     *  there. */
    private interface OfAComposedRow {
        void check(String model, String point, String row);
    }

    /**
     * Every row every one of these models composes, one at a time.
     *
     * <p>One row per compilation and not all of a model's rows at once. Which point a row met is the
     * claim being made, and a model holding every row it composed would have each point met by
     * whichever row happened to reach it.
     */
    private static void forEachComposedRow(OfAComposedRow held) {
        EveryDeclaredFormIsMeasuredAtItsOwnCoefficientsTest.MEASURED.forEach((operation, observed) -> {
            String model = EveryDeclaredFormIsMeasuredAtItsOwnCoefficientsTest.modelOf(observed);
            for (BorderAssessment border : lines(model)) {
                border.items().forEach((role, item) -> {
                    if (item instanceof ItemAssessment.Owed owed
                            && owed.searches().only() instanceof ItemAssessment.Attempt.Built built) {
                        held.check(model, border.label() + " " + border.border().named(role),
                                written(built.row()));
                    }
                });
            }
        });
    }

    /** A composed row's inputs, as an example line writes them. */
    private static String written(Generator.GeneratedRow row) {
        return "(" + String.join(", ",
                row.inputs().stream().map(FixtureTemplate::text).toList()) + ")";
    }

    private static String example(String row) {
        return "\nexample f\n    | " + row + " -> " + WHATEVER + "\n";
    }

    /** Whether the point is met, read off the item rather than out of a report's text. */
    private static boolean met(List<BorderAssessment> lines, String point) {
        for (BorderAssessment border : lines) {
            for (Map.Entry<DomainPoint, ItemAssessment> each : border.items().entrySet()) {
                if (!point.equals(border.label() + " "
                        + border.border().named(each.getKey()))) {
                    continue;
                }
                return each.getValue() instanceof ItemAssessment.Owed owed
                        && owed.hasRowWitness();
            }
        }
        return false;
    }

    /** What the compiler says about a model, less the one thing an invented answer causes. */
    private static List<String> otherThanTheAnswer(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<String> said = new ArrayList<>();
        for (Map.Entry<SourceId, List<Located>> each : compilation.diagnostics().entrySet()) {
            for (Located found : each.getValue()) {
                if (!THE_ANSWER_DISAGREES.equals(found.diagnostic().code())) {
                    said.add(found.diagnostic().code());
                }
            }
        }
        return said;
    }

    /** The lines the behavior's positions met, whosever the row at each point is. */
    private static List<BorderAssessment> lines(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, () -> "the model under test compiles: " + source);
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, () -> "f was measured: " + source);
        return lines;
    }

    private static PartitionEvidence measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + source);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + source);
        return measured;
    }
}
