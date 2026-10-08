package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Carrier;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition on a container's elements is composed as what it says — every element, or some —
 * and closed only where the rules of the elements leave it nothing.
 *
 * <p>Every element meeting a condition is met by a container holding none, and is one of two ways
 * and not two demands. Some element meeting one is met by one element, and a way that also holds a
 * condition on the element it is walking may be about another one — so nothing the way leaves is a
 * proof, and what the declarations leave every element is.
 */
class AConditionOnAContainersElementsIsComposedAsWhatItSaysTest {

    private static final String MODEL = """
            module probe.elements

            data Item = { n: Int }
                invariant n >= -5 && n <= 5

            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B
            data C

            behavior decide : (x: Input) -> A | B | C
            let decide (x) =
                if List.length(x.items) > 2 then C
                else if List.all(i -> i.n > 5, x.items) then
                    if x.gate > 0 then A else B
                else C

            behavior nonePastFive : (x: Input) -> Bool
            let nonePastFive (x) = List.all(i -> i.n > 5, x.items)

            behavior allPositive : (x: Input) -> Bool
            let allPositive (x) = List.all(i -> i.n > 0, x.items)

            behavior somePastFive : (x: Input) -> Bool
            let somePastFive (x) = List.any(i -> i.n > 5, x.items)

            behavior somePositive : (x: Input) -> Bool
            let somePositive (x) = List.any(i -> i.n > 0, x.items)

            behavior someNegative : (x: Input) -> Bool
            let someNegative (x) = List.any(i -> i.n < 0, x.items)

            behavior atLeastOne : (x: Input) -> Bool
            let atLeastOne (x) = List.length(x.items) >= 1
            """;

    /** Where no element can meet it, a row past it holds no element. */
    @Test
    void whereNoElementCanMeetEveryElementTheRowHoldsNone() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast(true, "nonePastFive"));
        assertEquals(List.of(), built.unrepresented().onTheWay(),
                "the condition was composed against: " + built.unrepresented());
        assertTrue(written(built).stream().anyMatch(each -> each.contains("items = []")),
                () -> "and the row holds no element: " + written(built));
    }

    /**
     * The container holding none is the other way of meeting every element, and not a second
     * thing asked of the size: beside a condition holding it to one or more, the size is still
     * asked for one.
     */
    @Test
    void theContainerHoldingNoneIsNotAskedOfTheSizeBesideTheElements() {
        OnTheWay.TakenIn atLeastOne = asked("atLeastOne");
        OnTheWay.TakenIn everyElement = asked("allPositive");
        RowDemand.ForAll every = assertInstanceOf(RowDemand.ForAll.class, everyElement.demand());
        NumericTerm.FromOnePosition size = every.holdingNone().orElseThrow().terms().iterator()
                .next().atOnePosition();
        List<OnTheWay.TakenIn> way = List.of(atLeastOne, everyElement);
        SearchRegion region = new WayToTheBorder(List.copyOf(way))
                .narrowing(domain("decide").quantities(rules()).region());
        Carrier on = domain("decide").quantities(rules()).ordersOf(size).answered();

        NumbersAskedFor asked = NumbersAskedFor.askedOf(size, region, on, way);
        assertTrue(asked.values().contains(new Level.OnACarrier(on, Count.of(1))),
                () -> "a list of one is a size both conditions leave: " + asked);
    }

    /** No element the rules allow meets it, so the way is closed — and said to be. */
    @Test
    void someElementNoElementCanBeClosesTheWay() {
        Generator.BoundaryAttempt.Unresolved closed = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class, composedPast(true, "somePastFive"));
        assertEquals(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE,
                closed.why().reason());
    }

    /**
     * Some element meeting it, on a way that already holds the element it walks to something else,
     * is not closed: two elements meet the two.
     */
    @Test
    void someElementBesideAnotherElementsConditionIsNotAProof() {
        Generator.BoundaryAttempt attempt = composedPast(false, "someNegative", "somePositive");
        assertTrue(attempt.unrepresented().onTheWay().stream()
                        .noneMatch(gap -> gap instanceof ReachabilityGap.ProvedImpossible),
                () -> "nothing the way leaves proves no row takes it: " + attempt.unrepresented());
    }

    /**
     * A row for `x.gate = 1` composed past what each of {@code behaviors} asks coming out true.
     *
     * @param inTheRegion whether what the first asks is taken into the region the row is looked
     *                    for in, as a condition the way to it holds of the element it walks
     */
    private static Generator.BoundaryAttempt composedPast(boolean inTheRegion,
                                                          String... behaviors) {
        List<OnTheWay.TakenIn> way = new ArrayList<>();
        for (String each : behaviors) {
            way.add(asked(each));
        }
        // The region a way leaves, as the way to a border is read into one: what it takes in
        // narrows it and what an element meets does not.
        SearchRegion region = new WayToTheBorder(List.copyOf(way))
                .narrowing(domain("decide").quantities(rules()).region());
        if (!inTheRegion) {
            RowDemand.Exists walked = assertInstanceOf(RowDemand.Exists.class,
                    way.removeFirst().demand());
            for (RowDemand.Relational each : walked.relations()) {
                region = each.constraint().narrowing(region);
            }
        }
        Axis gate = axisAt("x.gate");
        return Generator.probeFixing(subject(), "x.gate = 1",
                Map.of(new RealizationTarget.AtOnePosition(gate.term()), Count.of(1)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain("decide").quantities(rules()).ordersOf(gate.term()).answered(),
                        Count.of(1)))),
                new Reachability.Reaching(region, Requirements.NONE, TruthsAsked.NONE,
                        List.copyOf(way)),
                Generator.CandidateCheck.ANY);
    }

    private static List<String> written(Generator.BoundaryAttempt.Built built) {
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    /** What {@code behavior}'s body asks of a row coming out true, as a condition on the way. */
    private static OnTheWay.TakenIn asked(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputDomain inputs = domain(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules()), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                inputs.reading(rules()), true);
        assertEquals(1, stated.size(), () -> "one condition: " + stated);
        return assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst());
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    private static String module() {
        return COMPILATION.modules().getFirst();
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
    }

    private static Hir.SpecBehavior spec(String behavior) {
        Prepared prepared = COMPILATION.db().ask(new Shapes.Prepared(module())).value();
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
    }

    private static InputDomain domain(String behavior) {
        InputDomain read = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static List<Axis> axes() {
        return COMPILATION.db().ask(new Adequacy.Divided(module(), "decide")).value().axes();
    }

    private static Axis axisAt(String path) {
        return axes().stream().filter(each -> each.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new IllegalStateException(
                        "the model under test is measured at " + path + ", and this run has "
                                + axes().stream().map(each -> each.id().toString()).toList()));
    }

    private static MeasuredInput subject() {
        List<String> names = new ArrayList<>();
        spec("decide").params().forEach(each -> names.add(each.name()));
        assertTrue(names.contains("x"), "the model takes the input the row is fixed in");
        return MeasuredInput.of("decide", domain("decide").reading(rules()),
                AxesATestWrote.asAMeasurement("decide", axes()));
    }
}
