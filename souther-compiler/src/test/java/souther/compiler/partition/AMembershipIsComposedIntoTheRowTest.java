package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Carrier;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A membership on the way is composed into the row: the value at one position written into the
 * container, or kept out of it, jointly with how many the container may hold.
 *
 * <p>The value may be of another parameter, which is then composed first; of the same parameter,
 * which is read off the one assignment; and a value no container can be built around is passed
 * over for the next. What the composing cannot build is said as that, and not as a condition this
 * compiler could not read.
 */
class AMembershipIsComposedIntoTheRowTest {

    private static final String MODEL = """
            module probe.compose

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name>, names: List<Name>, picked: Name }

            data Digit = Int
                invariant value >= 0 && value <= 9

            data Box = { held: List<Digit> }

            data Pair = { seen: Set<Bool> }
                invariant Set.size(seen) >= 2

            behavior direct : (lead: Lead, priority: Name) -> Bool
            let direct (lead, priority) = Set.contains(priority, lead.campaigns)

            behavior listed : (lead: Lead) -> Bool
            let listed (lead) = List.contains(lead.picked, lead.names)

            behavior boxed : (box: Box, n: Digit) -> Bool
            let boxed (box, n) = List.contains(n, box.held)

            data Single = { held: List<Digit> }
                invariant List.length(held) <= 1

            behavior both : (single: Single, n: Digit, m: Digit) -> Bool
            let both (single, n, m) = List.contains(n, single.held) && List.contains(m, single.held)

            behavior twice : (single: Single, n: Digit) -> Bool
            let twice (single, n) = List.contains(n, single.held) && List.contains(n, single.held)

            data Outer = { held: List<List<Digit>> }

            behavior chained : (outer: Outer, box: Box, n: Digit) -> Bool
            let chained (outer, box, n) =
                List.contains(n, box.held) && List.contains(box.held, outer.held)

            data Crowd = { campaigns: Set<Name> }
                invariant Set.size(campaigns) >= 1

            behavior crowded : (crowd: Crowd, priority: Name) -> Bool
            let crowded (crowd, priority) = Set.contains(priority, crowd.campaigns)

            behavior paired : (pair: Pair, b: Bool) -> Bool
            let paired (pair, b) = Set.contains(b, pair.seen)
            """;

    /**
     * Holding a value of another parameter: that parameter is composed first, though it is
     * declared after the container, and its value is written into the container.
     */
    @Test
    void aContainerHoldsTheValueAnotherParameterWasComposedAs() {
        List<String> row = written(composedPast("direct", true, Generator.CandidateCheck.ANY));
        assertTrue(elementsOf(row.get(0), "campaigns").contains(row.get(1)),
                () -> "the campaigns hold the priority: " + row);
    }

    /** Holding nothing equal to it, and where the rules ask for no element, holding none. */
    @Test
    void aContainerKeptFromAValueHoldsNothingEqualToIt() {
        List<String> row = written(composedPast("direct", false, Generator.CandidateCheck.ANY));
        assertFalse(elementsOf(row.get(0), "campaigns").contains(row.get(1)),
                () -> "the campaigns do not hold the priority: " + row);
        assertEquals(List.of(), elementsOf(row.get(0), "campaigns"),
                () -> "and the rules ask for none of them: " + row);
    }

    /** Kept from a value where the rules ask for one at the fewest: one other than it. */
    @Test
    void aContainerKeptFromAValueAndHoldingOneHoldsAnother() {
        List<String> row = written(composedPast("crowded", false, Generator.CandidateCheck.ANY));
        List<String> held = elementsOf(row.get(0), "campaigns");
        assertEquals(1, held.size(), () -> "one, as the rules ask: " + row);
        assertFalse(held.contains(row.get(1)), () -> "and not the priority: " + row);
    }

    /**
     * A container whose size a point fixes is built to that size holding the value, rather than
     * written as the values standing for the size — which hold whatever they happen to.
     */
    @Test
    void aContainerWhoseSizeIsFixedHoldsTheValueAtThatSize() {
        RowDemand.Exists some = assertInstanceOf(RowDemand.Exists.class,
                ((OnTheWay.TakenIn) stated("direct", true).getFirst()).demand());
        NumericTerm size = some.holdingOne().orElseThrow().terms().iterator().next();
        List<OnTheWay.TakenIn> way = List.of((OnTheWay.TakenIn) stated("direct", true).getFirst());
        SearchRegion region = new WayToTheBorder(List.copyOf(way))
                .narrowing(domain("direct").quantities(rules()).region());
        Carrier on = domain("direct").quantities(rules()).ordersOf(size.atOnePosition())
                .answered();
        List<String> row = written(Generator.probeFixing(subject("direct"), "size 2",
                Map.of(new RealizationTarget.AtOnePosition(size.atOnePosition()), Count.of(2)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(on, Count.of(2)))),
                new Reachability.Reaching(region, Requirements.NONE, TruthsAsked.NONE, way),
                Generator.CandidateCheck.ANY));
        List<String> campaigns = elementsOf(row.get(0), "campaigns");
        assertEquals(2, campaigns.size(), () -> "the size the point fixes: " + row);
        assertTrue(campaigns.contains(row.get(1)), () -> "holding the priority: " + row);
    }

    /** The value at another position of the same parameter is read off the same assignment. */
    @Test
    void aValueOfTheSameParameterIsTheOneItsOwnPositionHolds() {
        String holds = written(composedPast("listed", true, Generator.CandidateCheck.ANY))
                .getFirst();
        assertTrue(elementsOf(holds, "names").contains(fieldOf(holds, "picked")),
                () -> "the names hold the one picked: " + holds);
        String keeps = written(composedPast("listed", false, Generator.CandidateCheck.ANY))
                .getFirst();
        assertFalse(elementsOf(keeps, "names").contains(fieldOf(keeps, "picked")),
                () -> "and are kept from it: " + keeps);
    }

    /**
     * A value the container cannot be built around is passed over for the next, rather than the
     * row given up at the first value of the parameter it is read off.
     */
    @Test
    void aValueNoContainerCanHoldIsPassedOverForTheNext() {
        // A rule of the box's that no first value of a digit meets: every element from five up.
        // Said by the check, as the model's own invariant would be when a row is decoded.
        Generator.CandidateCheck boxes = Generator.CandidateCheck.refusing(
                (p, candidate) -> p == 0 && !elementsOf(candidate.text(), "held").stream()
                        .allMatch(each -> digitOf(each) >= 5)
                        ? Optional.of("an element under five") : Optional.empty());
        List<String> row = written(composedPast("boxed", true, boxes));
        assertTrue(elementsOf(row.get(0), "held").contains(row.get(1)),
                () -> "the box holds the number: " + row);
    }

    /**
     * Two values a list is to hold that are one value are one element: holding a value is a
     * question about which values are in it, and a list holding one holds it however many times
     * it was asked to.
     */
    @Test
    void valuesToHoldThatAreOneValueAreOneElement() {
        List<String> row = written(composedPast("both", true, Generator.CandidateCheck.ANY));
        List<String> held = elementsOf(row.get(0), "held");
        assertTrue(held.contains(row.get(1)) && held.contains(row.get(2)),
                () -> "the list holds both: " + row);
        List<String> again = written(composedPast("twice", true, Generator.CandidateCheck.ANY));
        assertTrue(elementsOf(again.get(0), "held").contains(again.get(1)),
                () -> "and one asked for twice is held: " + again);
    }

    /**
     * A value passed over for one a parameter further along could not be composed under, where
     * that one is handed it through a parameter between them.
     *
     * <p>The number is written into the box, and the box into the outer list. An outer list the
     * rules refuse for the box the first number made is one another number may not make, so it is
     * the number that is tried again — though the outer list reads only the box.
     */
    @Test
    void aValueIsPassedOverForOneTheParameterItReachesThroughAnotherCameToNothingUnder() {
        Generator.CandidateCheck outers = Generator.CandidateCheck.refusing(
                (p, candidate) -> p == 0 && !digitsIn(candidate.text()).stream()
                        .allMatch(each -> each >= 5)
                        ? Optional.of("a digit under five") : Optional.empty());
        List<String> row = written(composedPast("chained", true, outers));
        assertTrue(digitOf(row.get(2)) >= 5, () -> "a number the outer list takes: " + row);
    }

    private static List<Integer> digitsIn(String written) {
        Matcher found = Pattern.compile("\\d+").matcher(written);
        List<Integer> out = new ArrayList<>();
        while (found.find()) {
            out.add(Integer.parseInt(found.group()));
        }
        return out;
    }

    /**
     * Where the element type has too few values to fill the container with none of them the one
     * kept out, that is a row nothing composes — and not a condition this compiler could not read.
     */
    @Test
    void tooFewValuesLeftIsWhatTheComposingCameTo() {
        Generator.BoundaryAttempt.Unresolved none = assertInstanceOf(
                Generator.BoundaryAttempt.Unresolved.class,
                composedPast("paired", false, Generator.CandidateCheck.ANY));
        assertNotEquals(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE,
                none.why().reason(), "nothing here proved the model leaves no row");
        assertEquals(List.of(), none.unrepresented().onTheWay(),
                () -> "the condition was read and composed against: " + none.unrepresented());
        assertInstanceOf(Generator.BoundaryAttempt.Built.class,
                composedPast("paired", true, Generator.CandidateCheck.ANY),
                "and the other way round there is room");
    }

    private static List<String> written(Generator.BoundaryAttempt attempt) {
        Generator.BoundaryAttempt.Built built =
                assertInstanceOf(Generator.BoundaryAttempt.Built.class, attempt);
        assertEquals(List.of(), built.unrepresented().onTheWay(),
                () -> "the condition was composed against: " + built.unrepresented());
        return built.row().inputs().stream().map(FixtureTemplate::text).toList();
    }

    /** The elements written in the collection at {@code field} of a record written as {@code
     *  record}. */
    private static List<String> elementsOf(String record, String field) {
        Matcher found = Pattern.compile(field + " = \\[([^]]*)]").matcher(record);
        assertTrue(found.find(), () -> field + " is written in " + record);
        String inside = found.group(1).trim();
        return inside.isEmpty() ? List.of()
                : Arrays.stream(inside.split(",")).map(String::trim).toList();
    }

    private static int digitOf(String written) {
        Matcher found = Pattern.compile("\\d+").matcher(written);
        assertTrue(found.find(), () -> "a digit is written in " + written);
        return Integer.parseInt(found.group());
    }

    private static String fieldOf(String record, String field) {
        Matcher found = Pattern.compile(field + " = ([^,}]*)").matcher(record);
        assertTrue(found.find(), () -> field + " is written in " + record);
        return found.group(1).trim();
    }

    private static Generator.BoundaryAttempt composedPast(String behavior, boolean holding,
                                                          Generator.CandidateCheck check) {
        List<OnTheWay.TakenIn> way = stated(behavior, holding).stream()
                .map(each -> assertInstanceOf(OnTheWay.TakenIn.class, each)).toList();
        SearchRegion region = new WayToTheBorder(List.copyOf(way))
                .narrowing(domain(behavior).quantities(rules()).region());
        return Generator.probeFixing(subject(behavior), "past " + behavior, Map.of(),
                NumbersAskedFor.ANYTHING,
                new Reachability.Reaching(region, Requirements.NONE, TruthsAsked.NONE, way),
                check);
    }

    /** What {@code behavior}'s body coming out {@code holding} asks of a row, one entry for each
     *  thing it asks. */
    private static List<OnTheWay> stated(String behavior, boolean holding) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, () -> "the model under test compiles: "
                + COMPILATION.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().literalMessage()
                        + " " + each.diagnostic().said())
                .toList());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputDomain inputs = domain(behavior);
        InputReading reading = inputs.reading(rules());
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                reading, holding);
        assertFalse(stated.isEmpty(), () -> "the body asks something of a row: " + behavior);
        return stated;
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

    private static InputDomain domain(String behavior) {
        InputDomain read = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static MeasuredInput subject(String behavior) {
        List<Axis> axes = COMPILATION.db().ask(new Adequacy.Divided(module(), behavior)).value()
                .axes();
        return MeasuredInput.of(behavior, domain(behavior).reading(rules()),
                AxesATestWrote.asAMeasurement(behavior, new ArrayList<>(axes)));
    }
}
