package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Symbols;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A run answers for everything its plan named, and offers no row nothing points at.
 *
 * <p>Two relations, each held as a set equality. The obligations against the answers, so a way out
 * of the search that writes no entry cannot be built at all — which is what a reader downstream
 * used to meet as an absence, and made a sentence out of saying this compiler had failed to say.
 * And the rows against the answers that point at them, in both directions: an answer naming a row
 * the offer does not hold reports an obligation met by a line nobody is shown, and a row nothing
 * points at is a line offered for nothing.
 *
 * <p>Held here rather than in the search. The search is one producer and there are others — the
 * rows could not be read, the classes would not link — and a rule kept where the searching happens
 * is one the others are free to break.
 */
class AFillIsTotalOverThePlanItWasAskedWithTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final Generator.ClassOwed A_CLASS =
            new Generator.ClassOwed(new AxisId("fee", "days"), "days/low");

    private static final Generator.ClassOwed ANOTHER_CLASS =
            new Generator.ClassOwed(new AxisId("fee", "days"), "days/high");

    private static final Generator.ArmOwed AN_ARM = new Generator.ArmOwed(1);

    private static final Generator.ArmOwed ANOTHER_ARM = new Generator.ArmOwed(2);

    private static final Generator.UnresolvedCombination NOTHING_CAME_OF_IT =
            new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED);

    @Test
    void aClassTheRunDidNotAnswerForIsRefused() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(A_CLASS), List.of()), new LinkedHashMap<>(), List.of(),
                        List.of(), Discharge.NOTHING));

        assertEquals(true, refused.getMessage().contains("days/low"), refused.getMessage());
    }

    @Test
    void anArmTheRunDidNotAnswerForIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(), List.of(AN_ARM)), new LinkedHashMap<>(), List.of(),
                        List.of(), Discharge.NOTHING));
    }

    @Test
    void aClassTheRunAnsweredForAndNobodyAskedAboutIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(A_CLASS), List.of()), new LinkedHashMap<>(), List.of(),
                        List.of(), new Discharge(
                                Map.of(A_CLASS, new ClassDisposition.Unresolved(NOTHING_CAME_OF_IT),
                                        ANOTHER_CLASS,
                                        new ClassDisposition.Unresolved(NOTHING_CAME_OF_IT)),
                                Map.of())));
    }

    @Test
    void anArmTheRunAnsweredForAndNobodyAskedAboutIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(), List.of(AN_ARM)), new LinkedHashMap<>(), List.of(),
                        List.of(), new Discharge(Map.of(),
                                Map.of(AN_ARM, new ArmDisposition.Unresolved(
                                                List.of(NOTHING_CAME_OF_IT)),
                                        ANOTHER_ARM, new ArmDisposition.Unresolved(
                                                List.of(NOTHING_CAME_OF_IT))))));
    }

    @Test
    void anAnswerPointingAtARowTheOfferDoesNotHoldIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(A_CLASS), List.of()), new LinkedHashMap<>(), List.of(),
                        List.of(), new Discharge(
                                Map.of(A_CLASS, new ClassDisposition.Built(new RowId(0))),
                                Map.of())));
    }

    @Test
    void aRowNothingPointsAtIsRefused() {
        LinkedHashMap<RowId, ComposedRow> composed = new LinkedHashMap<>();
        composed.put(new RowId(0), new ComposedRow(List.of(FixtureTemplate.integer(1))));

        assertThrows(IllegalStateException.class,
                () -> new FillResult(planOver(List.of(A_CLASS), List.of()), composed, List.of(),
                        List.of(), new Discharge(
                                Map.of(A_CLASS,
                                        new ClassDisposition.Unresolved(NOTHING_CAME_OF_IT)),
                                Map.of())));
    }

    /** One answer per obligation and one row apiece, which is what a run that composed both looks
     *  like. */
    @Test
    void aRunThatAnsweredForEverythingItWasAskedIsBuilt() {
        LinkedHashMap<RowId, ComposedRow> composed = new LinkedHashMap<>();
        composed.put(new RowId(0), new ComposedRow(List.of(FixtureTemplate.integer(1))));

        FillResult filled = new FillResult(planOver(List.of(A_CLASS), List.of(AN_ARM)), composed,
                List.of(), List.of(), new Discharge(
                        Map.of(A_CLASS, new ClassDisposition.Built(new RowId(0))),
                        Map.of(AN_ARM, new ArmDisposition.Built(new RowId(0)))));

        assertEquals(1, filled.rows().size(), "one line, offered for both");
    }

    private static GenerationPlan planOver(List<Generator.ClassOwed> classes,
                                           List<Generator.ArmOwed> arms) {
        Axis days = new Axis(new AxisId("fee", "days"),
                new souther.compiler.inputs.NumericTerm.ValueOf(
                        souther.compiler.inputs.TermPath.of("days")),
                Type.INT, List.of(divided("days/low", 1), divided("days/high", 9)), List.of());
        Generator.Subject subject = new Generator.Subject("fee",
                new BehaviorInputs(List.of("days"), List.of(Type.INT), SYMBOLS,
                        ReadAs.THE_COMPILATION_DOES),
                List.of(days), HeldCounts.NONE);
        return new GenerationPlan(subject, classes, arms);
    }

    private static PartitionClass divided(String id, long value) {
        return PartitionClass.of(id, id, new Recognition.Nothing(),
                RepresentativeSource.of(List.of(FixtureTemplate.integer(value))));
    }
}
