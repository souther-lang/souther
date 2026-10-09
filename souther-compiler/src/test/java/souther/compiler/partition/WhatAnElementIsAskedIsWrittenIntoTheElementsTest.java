package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a quantifier asks of an element is written into the elements of a row: a truth or a case of
 * a position inside the element, one of several things the element meets, what a quantifier over
 * a container inside the element asks of that container's elements, and what every element meets
 * about the numbers beside it.
 *
 * <p>A composer writes the elements of a container alike, so what it writes is a row whose
 * elements all meet what one is asked. Two elements asked for two things are then a row it did
 * not write, and that is said as its own answer — never as a way the model leaves no row along.
 */
class WhatAnElementIsAskedIsWrittenIntoTheElementsTest {

    private static final String MODEL = """
            module probe.elementwrites

            data Tier = Gold | Plain

            data Item = { n: Int, paid: Bool, tier: Tier }
                invariant n >= -10 && n <= 10

            data Group = { items: List<Item> }

            data Input = { items: List<Item>, groups: List<Group>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B

            behavior decide : (x: Input) -> A | B
            let decide (x) = if x.gate > 0 then A else B

            behavior someUnpaid : (x: Input) -> Bool
            let someUnpaid (x) = List.any(i -> Bool.not(i.paid), x.items)

            behavior everyUnpaid : (x: Input) -> Bool
            let everyUnpaid (x) = List.all(i -> Bool.not(i.paid), x.items)

            behavior someGold : (x: Input) -> Bool
            let someGold (x) = List.any(i ->
                match i.tier with
                    | Gold -> true
                    | Plain -> false, x.items)

            behavior somePlain : (x: Input) -> Bool
            let somePlain (x) = List.any(i ->
                match i.tier with
                    | Gold -> false
                    | Plain -> true, x.items)

            behavior someFarOut : (x: Input) -> Bool
            let someFarOut (x) = List.any(i -> i.n > 5 || i.n < -5, x.items)

            behavior someBeyondTheRules : (x: Input) -> Bool
            let someBeyondTheRules (x) = List.any(i -> i.n > 10 || i.n < -10, x.items)

            behavior someGroupWithADearOne : (x: Input) -> Bool
            let someGroupWithADearOne (x) =
                List.any(g -> List.any(i -> i.n > 3, g.items), x.groups)

            behavior someGroupAllDear : (x: Input) -> Bool
            let someGroupAllDear (x) =
                List.any(g -> List.all(i -> i.n > 3, g.items), x.groups)

            behavior everyAboveTheGate : (x: Input) -> Bool
            let everyAboveTheGate (x) = List.all(i -> i.n > x.gate, x.items)
            """;

    /**
     * Some element holding a truth is a row with an element holding it — asked for the value a
     * composer writes no element with of its own accord, so the row tells the two apart.
     */
    @Test
    void aTruthOfSomeElementIsWrittenIntoTheElement() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast("someUnpaid"));
        assertTrue(written(built).stream().anyMatch(each -> each.contains("paid = false")),
                () -> "an element of the row is unpaid: " + written(built));
    }

    /**
     * Every element holding a truth is a row none of whose elements holds the other value — asked
     * beside some element of a case, so the row holds an element to ask it of.
     */
    @Test
    void aTruthOfEveryElementIsWrittenIntoEachOfThem() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast("everyUnpaid", "someGold"));
        assertTrue(written(built).stream().anyMatch(each -> each.contains("Gold")
                        && each.contains("paid = false") && !each.contains("paid = true")),
                () -> "every element of the row is unpaid: " + written(built));
    }

    /** Some element of a case is a row with an element of that case. */
    @Test
    void aCaseOfSomeElementIsWrittenIntoTheElement() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast("someGold"));
        assertTrue(written(built).stream().anyMatch(each -> each.contains("Gold")),
                () -> "an element of the row is gold: " + written(built));
    }

    /**
     * Some element of one case beside some element of the other is two elements, which a row of
     * elements written alike is not — and not a way no row takes.
     */
    @Test
    void twoElementsAskedForTwoCasesAreNotAProof() {
        Generator.BoundaryAttempt attempt = composedPast("someGold", "somePlain");
        Generator.BoundaryAttempt.Unresolved unresolved =
                assertInstanceOf(Generator.BoundaryAttempt.Unresolved.class, attempt);
        assertFalse(unresolved.why().reason().provesInfeasible(),
                () -> "elements that differ meet both: " + unresolved.why());
        assertTrue(attempt.unrepresented().onTheWay().stream()
                        .noneMatch(gap -> gap instanceof ReachabilityGap.ProvedImpossible),
                () -> "and nothing on the way is proved closed: " + attempt.unrepresented());
    }

    /** Some element meeting one of two things is looked for along each, and found along one. */
    @Test
    void oneOfSeveralThingsSomeElementMeetsIsFoundAlongOneOfThem() {
        List<Generator.BoundaryAttempt> along = composedAlongEach("someFarOut");
        assertEquals(2, along.size(), () -> "a way for each of the two: " + along);
        assertTrue(along.stream().anyMatch(Generator.BoundaryAttempt.Built.class::isInstance),
                () -> "a row is written along one of them: " + along);
    }

    /** And where the rules leave no element either of them, each way is closed by the rules. */
    @Test
    void oneOfSeveralThingsNoElementCanBeIsClosedAlongEach() {
        List<Generator.BoundaryAttempt> along = composedAlongEach("someBeyondTheRules");
        assertEquals(2, along.size(), () -> "a way for each of the two: " + along);
        for (Generator.BoundaryAttempt each : along) {
            Generator.BoundaryAttempt.Unresolved closed =
                    assertInstanceOf(Generator.BoundaryAttempt.Unresolved.class, each);
            assertEquals(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE,
                    closed.why().reason(), () -> "the rules leave it nothing: " + closed);
        }
    }

    /** What some element's own elements meet is written into the elements of an element. */
    @Test
    void aQuantifierInsideAnElementIsWrittenIntoItsElements() {
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast("someGroupWithADearOne"));
        assertTrue(written(built).stream().anyMatch(each -> each.matches(
                        "(?s).*groups = \\[Group \\{ items = \\[Item \\{ n = ([4-9]|10),.*")),
                () -> "a group of the row holds an item past three: " + written(built));
    }

    /**
     * Every element of a container inside the element meeting something is two ways: elements
     * that meet it, and the inner container holding none.
     */
    @Test
    void everyElementOfAContainerInsideAnElementIsTwoWays() {
        List<OnTheWay> stated = stated("someGroupAllDear");
        OnTheWay.OneOf ways = assertInstanceOf(OnTheWay.OneOf.class, stated.getFirst(),
                "the inner list's elements meeting it, or the inner list holding none");
        assertEquals(2, ways.alternatives().size(), () -> "two ways: " + ways);
        assertTrue(composedAlongEach("someGroupAllDear").stream()
                        .allMatch(Generator.BoundaryAttempt.Built.class::isInstance),
                () -> "a row is written along each");
    }

    /** What every element meets about a number beside it places that number with the element. */
    @Test
    void everyElementMeetingWhatIsBesideItPlacesWhatIsBesideIt() {
        OnTheWay.TakenIn taken = assertInstanceOf(OnTheWay.TakenIn.class,
                stated("everyAboveTheGate").getFirst());
        assertInstanceOf(RowDemand.ForAll.class, taken.demand(),
                "every element meets it, or the list holds none");
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, composedPast("everyAboveTheGate"));
        assertTrue(written(built).stream().allMatch(each -> each.contains("gate = 1")),
                () -> "the gate the row is fixed at: " + written(built));
    }

    /** A row for `x.gate = 1` composed past what each of {@code behaviors} asks coming out
     *  true, along the one way they make. */
    private static Generator.BoundaryAttempt composedPast(String... behaviors) {
        List<OnTheWay> way = new ArrayList<>();
        for (String each : behaviors) {
            way.addAll(stated(each));
        }
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(List.copyOf(way)), declarations()));
        return probed(reaching);
    }

    /** The same along each way {@code behavior} coming out true splits the way into. */
    private static List<Generator.BoundaryAttempt> composedAlongEach(String behavior) {
        Reachability.Reaching reaching = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(stated(behavior)), declarations()));
        List<Generator.BoundaryAttempt> out = new ArrayList<>();
        reaching.along().forEach(one -> out.add(probed(one)));
        return out;
    }

    private static Generator.BoundaryAttempt probed(Reachability.Reaching reaching) {
        Axis gate = axisAt("x.gate");
        return Generator.probeFixing(subject(), "x.gate = 1",
                Map.of(new RealizationTarget.AtOnePosition(gate.term()), Count.of(1)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain("decide").quantities(rules()).ordersOf(gate.term()).answered(),
                        Count.of(1)))),
                reaching, Generator.CandidateCheck.ANY);
    }

    private static SearchRegion declarations() {
        return domain("decide").quantities(rules()).region();
    }

    private static List<String> written(Generator.BoundaryAttempt.Built built) {
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    /** What {@code behavior}'s body asks of a row coming out true, as conditions on the way. */
    private static List<OnTheWay> stated(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputDomain inputs = domain(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules()), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        InputReading reading = inputs.reading(rules());
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                reading, true, WhatConditionsState.of(reading));
        assertEquals(1, stated.size(), () -> "one condition: " + stated);
        return stated;
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return made;
    }

    private static String module() {
        return COMPILATION.modules().getFirst();
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
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
                        "the model under test is measured at " + path));
    }

    private static MeasuredInput subject() {
        return MeasuredInput.of("decide", domain("decide").reading(rules()),
                AxesATestWrote.asAMeasurement("decide", axes()));
    }
}
