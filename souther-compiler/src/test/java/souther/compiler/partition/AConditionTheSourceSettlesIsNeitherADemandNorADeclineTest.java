package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
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
 * A condition whose answer is the same for every row asks nothing of a row the way it always comes
 * out, closes the way it never does, and is never a condition this compiler could not state.
 *
 * <p>Held where it would have gone wrong. A predicate fixed at one answer, read for the relations
 * it states, states none — and came back declined, so a way past {@code List.any(_ -> true, xs)}
 * failing was a way this compiler fell short on rather than a container holding none, and the way
 * past {@code List.all(_ -> true, xs)} failing was one a row was owed for. The quantifier comes to
 * the container's size where the predicate is fixed: some element meeting what every element
 * meets is the container holding one, and every element meeting what none meets is it holding
 * none.
 */
class AConditionTheSourceSettlesIsNeitherADemandNorADeclineTest {

    private static final String MODEL = """
            module probe.settled

            data Item = { n: Int }
                invariant n >= -5 && n <= 5

            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B
            data C

            behavior decideEmpty : (x: Input) -> A | B | C
            let decideEmpty (x) =
                if List.length(x.items) > 2 then C
                else if List.any(i -> true, x.items) then A
                else if x.gate > 0 then B
                else C

            behavior decideNever : (x: Input) -> A | B | C
            let decideNever (x) =
                if List.all(i -> true, x.items) then A
                else if x.gate > 0 then B
                else C

            behavior decideCancelled : (x: Input) -> A | B | C
            let decideCancelled (x) =
                if x.gate - x.gate > 0 then A
                else if x.gate > 0 then B
                else C

            behavior someHolds : (x: Input) -> Bool
            let someHolds (x) = List.any(i -> true, x.items)

            behavior everyFails : (x: Input) -> Bool
            let everyFails (x) = List.all(i -> false, x.items)

            behavior everyHolds : (x: Input) -> Bool
            let everyHolds (x) = List.all(i -> true, x.items)

            behavior noneHolds : (x: Input) -> Bool
            let noneHolds (x) = List.any(i -> false, x.items)

            behavior somePositiveAndTrue : (x: Input) -> Bool
            let somePositiveAndTrue (x) = List.any(i -> true && i.n > 0, x.items)

            behavior somePositiveOrFalse : (x: Input) -> Bool
            let somePositiveOrFalse (x) = List.any(i -> false || i.n > 0, x.items)

            behavior holdsOne : (x: Input) -> Bool
            let holdsOne (x) = List.length(x.items) >= 1

            behavior holdsNone : (x: Input) -> Bool
            let holdsNone (x) = List.length(x.items) <= 0
            """;

    /**
     * A quantifier over a predicate that always holds, or never does, is what it says of the
     * container's size, each way it comes out — the same demand the size compared outright is.
     */
    @Test
    void aFixedPredicateComesToTheSizeOfTheContainer() {
        RowDemand holdingOne = demandOf("holdsOne", true);
        RowDemand holdingNone = demandOf("holdsNone", true);
        assertEquals(holdingOne, demandOf("someHolds", true),
                "some element meeting what every element meets is the list holding one");
        assertEquals(holdingNone, demandOf("someHolds", false),
                "and no element meeting it is the list holding none");
        assertEquals(holdingNone, demandOf("everyFails", true),
                "every element meeting what none meets is the list holding none");
        assertEquals(holdingOne, demandOf("everyFails", false),
                "and some element failing what every element fails is the list holding one");
    }

    /**
     * Every element meeting what every element meets asks nothing, and some element meeting what
     * none meets is no row's — and neither is declined.
     */
    @Test
    void aFixedPredicateTheContainerCannotChangeIsSettled() {
        assertEquals(new OnTheWay.Settled(occurrence("everyHolds"), anchor("everyHolds"), true),
                only("everyHolds", true), "true whatever the list holds");
        assertEquals(false, settled("everyHolds", false).thisWay(),
                "so no row brings it out false");
        assertEquals(true, settled("noneHolds", false).thisWay(),
                "false whatever the list holds");
        assertEquals(false, settled("noneHolds", true).thisWay(),
                "so no row brings it out true");
    }

    /**
     * A part of a predicate the source settles is not what the element is asked: beside the rest
     * of a conjunction, one that always holds asks nothing, and of a disjunction, one that never
     * holds leaves the rest as all that is said — the same element relation either way.
     */
    @Test
    void aPartOfAPredicateTheSourceSettlesLeavesWhatTheRestAsks() {
        RowDemand.Exists and = assertInstanceOf(RowDemand.Exists.class,
                demandOf("somePositiveAndTrue", true));
        assertEquals(1, and.ofAnElement().size(), () -> "only what the element is asked: " + and);
        assertEquals(and, demandOf("somePositiveOrFalse", true),
                "and one of two things, one of which never holds, is the other");
    }

    /**
     * Past a container holding none, a row for the next border is composed with no element, and
     * nothing on the way is left unstated.
     *
     * <p>The body measures the list's size elsewhere, which is what puts a size a row can be
     * composed at: where nothing measures it the demand is still the container holding none, and
     * composing one is the question the size of a container nothing measures leaves open.
     */
    @Test
    void theWayPastSomeElementMeetingWhatAlwaysHoldsFailingIsTheEmptyContainer() {
        WayToTheBorder way = wayToTheGate("decideEmpty");
        assertEquals(List.of(), way.declined(), () -> "nothing on the way is declined: " + way);
        RowDemand holdingNone = demandOf("holdsNone", true);
        assertTrue(way.takenIn().stream().anyMatch(each -> each.demand().equals(holdingNone)),
                () -> "the list holding none is what the composer is handed: " + way);
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedFor(way));
        assertEquals(List.of(), built.unrepresented().onTheWay(),
                () -> "composed against the whole way: " + built.unrepresented());
        assertTrue(written(built).stream().anyMatch(each -> each.contains("items = []")),
                () -> "and the row holds no element: " + written(built));
    }

    /** Past every element meeting what always holds failing, no row arrives — and that is said. */
    @Test
    void theWayPastSomethingThatNeverComesOutThatWayIsOneNoRowTakes() {
        WayToTheBorder way = wayToTheGate("decideNever");
        assertEquals(List.of(), way.declined(), () -> "nothing on the way is declined: " + way);
        assertInstanceOf(Reachability.NothingComesOutThatWay.class,
                Reachability.of(way, domain("decideNever").quantities(rules()).region()),
                () -> "a way no row takes: " + way);
    }

    /**
     * A comparison whose two sides differ by the same amount on every row draws no rule down the
     * side no row takes, and is no column of the rules down the side every row takes.
     */
    @Test
    void aComparisonThatCancelsDrawsNoRuleDownTheSideNoRowTakes() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(MODEL, "decideCancelled");
        assertEquals(2, rules.size(), () -> "the gate either way, and nothing else: " + rules);
        assertTrue(rules.stream().allMatch(rule -> rule.inOrder().size() == 1),
                () -> "each turns on the gate alone: " + rules);
    }

    private static OnTheWay.Settled settled(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.Settled.class, only(behavior, holding),
                () -> behavior + " coming out " + holding + " is settled");
    }

    private static RowDemand demandOf(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.TakenIn.class, only(behavior, holding),
                () -> behavior + " coming out " + holding + " asks something of a row").demand();
    }

    private static OnTheWay only(String behavior, boolean holding) {
        List<OnTheWay> stated = ReachingCuts.stating(conditionOf(behavior),
                domain(behavior).reading(rules()), holding);
        assertEquals(1, stated.size(), () -> behavior + " is one condition: " + stated);
        return stated.getFirst();
    }

    private static ConditionOccurrence occurrence(String behavior) {
        return conditionOf(behavior).occurrence();
    }

    private static ConditionReportAnchor anchor(String behavior) {
        return conditionOf(behavior).anchor();
    }

    private static Condition conditionOf(String behavior) {
        AnalysisBody analysis = checked().analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(
                domain(behavior).parameterReads(), domain(behavior).declared(rules()),
                ElementBindings.of(analysis, rules().newtypes()));
        return Condition.of(analysis.core(), reads, rules().symbols(), rules().newtypes(),
                new ConditionNumbering(module(), behavior));
    }

    /** The way the walk of {@code behavior} took to the one comparison its body writes. */
    private static WayToTheBorder wayToTheGate(String behavior) {
        Bodies.Elaborated checked = checked();
        Core body = checked.behaviorBodies().get(behavior);
        CoverageSites.Plan plan = checked.plan();
        GuardThresholds.Guards guards = ThresholdFixtures.guardsOf(behavior,
                checked.analysisBodies().get(behavior), body, plan, domain(behavior), rules());
        List<List<OnTheWay>> ways = ReachingAccounts.filedFor(guards.reaching(), body);
        assertEquals(1, ways.size(), () -> "one comparison is past a condition: " + ways);
        return new WayToTheBorder(ways.getFirst());
    }

    /** A row for `x.gate = 1` composed against {@code way}. */
    private static Generator.BoundaryAttempt composedFor(WayToTheBorder way) {
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(way, domain("decideEmpty").quantities(rules()).region()));
        Axis gate = axisAt("x.gate");
        return Generator.probeFixing(subject(), "x.gate = 1",
                Map.of(new RealizationTarget.AtOnePosition(gate.term()), Count.of(1)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain("decideEmpty").quantities(rules()).ordersOf(gate.term())
                                .answered(),
                        Count.of(1)))),
                reaching, Generator.CandidateCheck.ANY);
    }

    private static List<String> written(Generator.BoundaryAttempt.Built built) {
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    private static Bodies.Elaborated checked() {
        Bodies.Elaborated checked = COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, "the model under test compiles");
        return checked;
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
        return COMPILATION.db().ask(new Adequacy.Divided(module(), "decideEmpty")).value().axes();
    }

    private static Axis axisAt(String path) {
        return axes().stream().filter(each -> each.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new IllegalStateException(
                        "the model under test is measured at " + path + ", and this run has "
                                + axes().stream().map(each -> each.id().toString()).toList()));
    }

    private static MeasuredInput subject() {
        List<String> names = new ArrayList<>();
        spec("decideEmpty").params().forEach(each -> names.add(each.name()));
        assertTrue(names.contains("x"), "the model takes the input the row is fixed in");
        return MeasuredInput.of("decideEmpty", domain("decideEmpty").reading(rules()),
                AxesATestWrote.asAMeasurement("decideEmpty", axes()));
    }
}
