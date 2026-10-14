package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DomainPoint;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container whose elements' values are past a figure of this compiler's is said to be stopped
 * at that figure, at every point of a line drawn on how many it holds.
 *
 * <p>A {@code Huge} holds more elements than a proposal holds, so no value of it is built, and no
 * container of two of them is either. Said as a point nothing could build a representative for,
 * the line is one the model leaves nothing at, when a row an author writes settles it.
 *
 * <p>The control is the same model one element short of the figure, where the container is built.
 */
class AContainerOfValuesPastAFigureIsSaidToBeStoppedThereTest {

    private static final String MODEL = """
            module p

            data Huge = List<Bool>
              invariant List.length(value) >= %d
            data Held = { h: Huge, n: Int }

            behavior f : (s: %s) -> Int
            let f (s) = if %s(s) == 2 then 1 else 0
            """;

    private static final int PAST = CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum() + 1;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static BorderAssessment lineAtTwo(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "p");
        assertNotNull(read, "the model under test compiles");
        for (BorderAssessment each : read.get("f")) {
            if (each.value().equals("2")) {
                return each;
            }
        }
        throw new AssertionError("no line at 2: " + read.get("f"));
    }

    /** The attempts at the line itself, which is the point a container of two is owed at. */
    private static List<ItemAssessment.Attempt> atTheLine(Compilation compilation) {
        ItemAssessment item = lineAtTwo(compilation).items().get(new DomainPoint.AtTheLine());
        assertTrue(item instanceof ItemAssessment.Owed, String.valueOf(item));
        return ((ItemAssessment.Owed) item).searches().each();
    }

    private static boolean stoppedAtTheFigure(List<ItemAssessment.Attempt> attempts) {
        return !attempts.isEmpty() && attempts.stream().allMatch(each ->
                each instanceof ItemAssessment.Attempt.Stopped stopped
                        && stopped.stoppedBy().written()
                                .contains(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS));
    }

    /** The set of the issue: two of them, built of values never built. */
    @Test
    void aSetOfTwoIsStoppedAtTheFigureItsElementsWerePast() {
        List<ItemAssessment.Attempt> attempts =
                atTheLine(measured(MODEL.formatted(PAST, "Set<Huge>", "Set.size")));

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /** A list of two, which is built of the value the element is offered and refused. */
    @Test
    void aListOfTwoIsStoppedAtTheFigureAndNotRefused() {
        List<ItemAssessment.Attempt> attempts =
                atTheLine(measured(MODEL.formatted(PAST, "List<Huge>", "List.length")));

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /** A map's values, and a record's field: the figure is the same however far in it was met. */
    @Test
    void aMapOrASetOfRecordsIsStoppedAtTheFigureToo() {
        for (List<String> each : List.of(List.of("Map<String, Huge>", "Map.size"),
                List.of("Set<Held>", "Set.size"))) {
            List<ItemAssessment.Attempt> attempts = atTheLine(measured(
                    MODEL.formatted(PAST, each.get(0), each.get(1))));

            assertTrue(stoppedAtTheFigure(attempts), () -> each + " " + attempts);
        }
    }

    /** One element short of the figure, the set is built and nothing stopped it. */
    @Test
    void aSetOfValuesAtTheFigureIsBuilt() {
        List<ItemAssessment.Attempt> attempts =
                atTheLine(measured(MODEL.formatted(PAST - 1, "Set<Huge>", "Set.size")));

        assertTrue(attempts.stream().anyMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                attempts::toString);
        assertFalse(attempts.stream().anyMatch(ItemAssessment.Attempt.Stopped.class::isInstance),
                attempts::toString);
    }

    /**
     * A row composed beside a value past the figure is a row. The list it holds is empty, and what
     * the figure kept from being built is nothing the row needed.
     */
    @Test
    void aRowThatNeedsNoValuePastTheFigureIsComposed() {
        Compilation compilation = measured("""
                module p

                data Huge = List<Bool>
                  invariant List.length(value) >= %d

                behavior f : (s: List<Huge>, n: Int) -> Int
                let f (s, n) = if n == 2 then 1 else 0
                """.formatted(PAST));
        List<ItemAssessment.Attempt> attempts = atTheLine(compilation);

        assertTrue(attempts.stream().allMatch(ItemAssessment.Attempt.Certified.class::isInstance),
                attempts::toString);
    }

    /**
     * A position beside the line whose own value is past the figure is offered only what its rules
     * refuse, which is refused before anything is composed — so what the offer met is the only
     * account of why, and the row at the line is said to be stopped there.
     */
    @Test
    void aPositionBesideTheLinePastTheFigureSaysTheFigure() {
        Compilation compilation = measured("""
                module p

                data Huge = List<Bool>
                  invariant List.length(value) >= %d

                behavior f : (s: Huge, n: Int) -> Int
                let f (s, n) = if n == 2 then 1 else 0
                """.formatted(PAST));
        List<ItemAssessment.Attempt> attempts = atTheLine(compilation);

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /**
     * A position beside the line that its rules ask to hold two of them is offered only what they
     * refuse, and the row at the line is said to be stopped at the figure rather than refused.
     */
    @Test
    void aPositionBesideTheLineHoldingTwoOfThemSaysTheFigure() {
        Compilation compilation = measured("""
                module p

                data Huge = List<Bool>
                  invariant List.length(value) >= %d
                data Two = Set<Huge>
                  invariant Set.size(value) >= 2

                behavior f : (s: Two, n: Int) -> Int
                let f (s, n) = if n == 2 then 1 else 0
                """.formatted(PAST));
        List<ItemAssessment.Attempt> attempts = atTheLine(compilation);

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /**
     * A container built around an element the line asks for, whose rules ask it to hold more than
     * a proposal holds, is not built — and the row at the line is said to be stopped at the figure
     * rather than refused, though every value at the element was one the rules admit.
     */
    @Test
    void aContainerFilledPastTheFigureAroundAnElementSaysTheFigure() {
        Compilation compilation = measured("""
                module p

                data R = { xs: List<Int> }
                  invariant List.length(xs) >= %d

                behavior f : (r: R) -> Int
                let f (r) = if List.any(x -> x == 2, r.xs) then 1 else 0
                """.formatted(PAST));
        List<ItemAssessment.Attempt> attempts = atTheLine(compilation);

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /**
     * Elements built around a number a total reads, whose other field is past the figure: each is
     * built with the value that field is offered, which its rules refuse, and the row at the line
     * is said to be stopped at the figure that kept the value they ask for out.
     */
    @Test
    void elementsBuiltAroundATotalSayTheFigureTheirOtherFieldWasPast() {
        Compilation compilation = measured("""
                module p

                data Huge = List<Bool>
                  invariant List.length(value) >= %d
                data Item = { q: Int, h: Huge }

                behavior f : (s: List<Item>) -> Int
                let f (s) = if List.sum(List.map(i -> i.q, s)) == 2 then 1 else 0
                """.formatted(PAST));
        List<ItemAssessment.Attempt> attempts = atTheLine(compilation);

        assertTrue(stoppedAtTheFigure(attempts), attempts::toString);
    }

    /**
     * And the rule of the decision that needs a list of two is said not to have been composed
     * against what this compiler stopped looking at, rather than against what nothing composed.
     */
    @Test
    void theDecisionRuleSaysTheFigureItWasComposedWithout() {
        String human = AdequacyReport.of(measured(MODEL.formatted(PAST, "List<Huge>",
                "List.length"))).human(SourceRendering.namedByIdentity(SourceLayouts.NONE));

        assertTrue(human.contains("not composed against: a condition on positions this compiler"
                + " stopped looking at (how many elements a proposed collection holds)"), human);
        assertFalse(human.contains("nothing here composed a value at"), human);
    }
}
