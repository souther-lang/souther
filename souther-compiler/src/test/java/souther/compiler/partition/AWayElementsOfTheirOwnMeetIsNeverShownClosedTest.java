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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No way some group of the input meets is shown to be one no row takes, whatever quantifiers over
 * the items inside a group ask: what two of them ask is met by two items, which may differ.
 *
 * <p>Held against the statements themselves. Each shape here is a quantifier over the groups whose
 * body is quantifiers over a group's items — or, a level further in, over the items of a sub of a
 * group — each asking its item one or two bounds, against a written number or against the
 * group's own {@code m}, which the body may bound as well. Whether some input meets one is worked
 * out by running it over every group of at most two items, with every {@code m}, of the values the
 * bounds tell apart, which is every way a group can meet a body of at most two quantifiers. Where
 * some group meets it, neither the way to it nor a row composed past it is said to be closed.
 * Where one quantifier asks its item what no item meets beside what the group meets, the way is
 * closed: what one quantifier asks is one item's, and what the group is asked holds of it.
 */
class AWayElementsOfTheirOwnMeetIsNeverShownClosedTest {

    /**
     * A bound on a number: {@code below} it is under {@code at}, otherwise at or over it — or,
     * {@code ofTheGroup}, under or at or over the group's {@code m}.
     */
    private record Bound(boolean below, int at, boolean ofTheGroup) {

        boolean holds(int n, int m) {
            int to = ofTheGroup ? m : at;
            return below ? n < to : n >= to;
        }

        String written(String number) {
            return number + " " + (below ? "<" : ">=") + " " + (ofTheGroup ? "g.m" : at);
        }
    }

    /** A quantifier over the items: every item or some item meets every one of {@code bounds}. */
    private record Quantifier(boolean every, List<Bound> bounds) {

        boolean holds(List<Integer> items, int m) {
            return every ? items.stream().allMatch(n -> meets(n, m))
                    : items.stream().anyMatch(n -> meets(n, m));
        }

        private boolean meets(int n, int m) {
            return bounds.stream().allMatch(bound -> bound.holds(n, m));
        }

        String written(String item, String container) {
            return "List." + (every ? "all" : "any") + "(" + item + " -> " + bounds.stream()
                    .map(bound -> bound.written(item + ".n")).collect(Collectors.joining(" && "))
                    + ", " + container + ")";
        }
    }

    /**
     * Quantifiers over the items of a group, or of a sub of a group where {@code deeper}, all of
     * which some group of the input meets together, beside the bounds {@code onTheGroup} asks of
     * its {@code m}.
     */
    private record Shape(boolean deeper, List<Bound> onTheGroup, List<Quantifier> quantifiers) {

        /** Whether some input meets it: some group, or some sub of one, whose items meet all. */
        boolean met() {
            return VALUES.stream().anyMatch(m ->
                    onTheGroup.stream().allMatch(bound -> bound.holds(m, m))
                    && ITEMS.stream().anyMatch(items ->
                            quantifiers.stream().allMatch(each -> each.holds(items, m))));
        }

        /** Whether it is one quantifier asking some item, which is one item's to meet. */
        boolean oneItem() {
            return quantifiers.size() == 1 && !quantifiers.getFirst().every();
        }

        String written() {
            String holder = deeper ? "s" : "g";
            List<String> parts = new ArrayList<>();
            onTheGroup.forEach(bound -> parts.add(bound.written("g.m")));
            for (int i = 0; i < quantifiers.size(); i++) {
                parts.add(quantifiers.get(i).written("a" + i, holder + ".items"));
            }
            String body = String.join(" && ", parts);
            return deeper ? "List.any(g -> List.any(s -> " + body + ", g.subs), x.groups)"
                    : "List.any(g -> " + body + ", x.groups)";
        }
    }

    /** The values the bounds tell apart, with one between each two of them. */
    private static final List<Integer> VALUES = List.of(-2, -1, 0, 1, 2);

    /** Every list of at most two of {@link #VALUES}. */
    private static final List<List<Integer>> ITEMS = items();

    private static List<List<Integer>> items() {
        List<List<Integer>> out = new ArrayList<>();
        out.add(List.of());
        for (int one : VALUES) {
            out.add(List.of(one));
            for (int two : VALUES) {
                out.add(List.of(one, two));
            }
        }
        return List.copyOf(out);
    }

    private static final List<Bound> BOUNDS = List.of(new Bound(true, 0, false),
            new Bound(true, 1, false), new Bound(false, 0, false), new Bound(false, 1, false));

    /** Bounds on an item against a written number, and against the group's number. */
    private static final List<Bound> AGAINST_THE_GROUP = List.of(new Bound(true, 0, false),
            new Bound(false, 1, false), new Bound(true, 0, true), new Bound(false, 0, true));

    /**
     * One quantifier of either kind asking two bounds, and two quantifiers of either kind asking
     * one each; and with a bound on the group's number, one quantifier of some item or two asking
     * bounds against it — a level in and two levels in.
     */
    private static final List<Shape> SHAPES = shapes();

    private static List<Shape> shapes() {
        List<Shape> out = new ArrayList<>();
        for (boolean deeper : List.of(false, true)) {
            for (boolean every : List.of(false, true)) {
                for (Bound first : BOUNDS) {
                    for (Bound second : BOUNDS) {
                        out.add(new Shape(deeper, List.of(),
                                List.of(new Quantifier(every, List.of(first, second)))));
                    }
                }
            }
            for (boolean firstEvery : List.of(false, true)) {
                for (boolean secondEvery : List.of(false, true)) {
                    for (Bound first : BOUNDS) {
                        for (Bound second : BOUNDS) {
                            out.add(new Shape(deeper, List.of(), List.of(
                                    new Quantifier(firstEvery, List.of(first)),
                                    new Quantifier(secondEvery, List.of(second)))));
                        }
                    }
                }
            }
            for (Bound group : BOUNDS) {
                for (Bound first : AGAINST_THE_GROUP) {
                    for (Bound second : AGAINST_THE_GROUP) {
                        out.add(new Shape(deeper, List.of(group),
                                List.of(new Quantifier(false, List.of(first, second)))));
                        out.add(new Shape(deeper, List.of(group), List.of(
                                new Quantifier(false, List.of(first)),
                                new Quantifier(false, List.of(second)))));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    @Test
    void noWaySomeGroupMeetsIsShownClosed() {
        List<String> closed = new ArrayList<>();
        for (int i = 0; i < SHAPES.size(); i++) {
            Shape shape = SHAPES.get(i);
            if (shape.met() && !(Reachability.of(new WayToTheBorder(stated(i)), declarations())
                    instanceof Reachability.Reaching)) {
                closed.add(shape.written());
            }
        }
        assertEquals(List.of(), closed, "some group meets each of these");
    }

    @Test
    void noRowComposedPastAWaySomeGroupMeetsIsShownImpossible() {
        List<String> impossible = new ArrayList<>();
        for (int i = 0; i < SHAPES.size(); i++) {
            Shape shape = SHAPES.get(i);
            if (!shape.met()) {
                continue;
            }
            Generator.BoundaryAttempt attempt = composedPast(i);
            boolean proved = (attempt instanceof Generator.BoundaryAttempt.Unresolved unresolved
                    && unresolved.why().reason().provesInfeasible())
                    || attempt.unrepresented().onTheWay().stream()
                            .anyMatch(ReachabilityGap.ProvedImpossible.class::isInstance);
            if (proved) {
                impossible.add(shape.written());
            }
        }
        assertEquals(List.of(), impossible, "some group meets each of these");
    }

    @Test
    void aWayNoItemOfOneQuantifierMeetsIsClosed() {
        List<String> open = new ArrayList<>();
        int asked = 0;
        for (int i = 0; i < SHAPES.size(); i++) {
            Shape shape = SHAPES.get(i);
            if (!shape.oneItem() || shape.met()) {
                continue;
            }
            asked++;
            if (Reachability.of(new WayToTheBorder(stated(i)), declarations())
                    instanceof Reachability.Reaching) {
                open.add(shape.written());
            }
        }
        assertTrue(asked > 0, "some shape asks one item what no item meets");
        assertEquals(List.of(), open, "no item meets what each of these asks one item");
    }

    /**
     * What is left of an element turns on what it was asked and not on the order: each two of the
     * things the ways here ask a group, taken in one after the other in either order, leave
     * nothing exactly where the two taken in at once do.
     */
    @Test
    void whatIsLeftOfAnElementDoesNotTurnOnTheOrderItIsAskedIn() {
        Set<RowDemand.AskedOfAnElement> pool = new LinkedHashSet<>();
        for (int i = 0; i < SHAPES.size(); i++) {
            if (stated(i).getFirst() instanceof OnTheWay.TakenIn(var _, RowDemand.Exists some)) {
                some.ofAnElement().asAsked().forEach(pool::addAll);
            }
        }
        WhatAnElementIsLeft nothingAsked = WhatAnElementIsLeft.of(declarations());
        List<String> differ = new ArrayList<>();
        int leaveNone = 0;
        for (RowDemand.AskedOfAnElement first : pool) {
            for (RowDemand.AskedOfAnElement second : pool) {
                if (first.equals(second)) {
                    continue;
                }
                boolean together = nothingAsked.with(List.of(first, second)).isEmpty();
                boolean inTurn = nothingAsked.with(List.of(first))
                        .flatMap(left -> left.with(List.of(second))).isEmpty();
                if (together) {
                    leaveNone++;
                }
                if (together != inTurn) {
                    differ.add(first + " then " + second);
                }
            }
        }
        assertTrue(leaveNone > 0, "some two of them leave no element");
        assertEquals(List.of(), differ, "taken in one after the other");
    }

    private static final String MODEL = """
            module probe.ownelements

            data Item = { n: Int }
                invariant n >= -10 && n <= 10

            data Sub = { items: List<Item> }

            data Group = { items: List<Item>, subs: List<Sub>, m: Int }

            data Input = { groups: List<Group>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B

            behavior decide : (x: Input) -> A | B
            let decide (x) = if x.gate > 0 then A else B

            %s
            """.formatted(IntStream.range(0, SHAPES.size())
            .mapToObj(i -> "behavior s" + i + " : (x: Input) -> Bool\nlet s" + i + " (x) = "
                    + SHAPES.get(i).written())
            .collect(Collectors.joining("\n\n")));

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return made;
    }

    /** A row for `x.gate = 1` composed past shape {@code i} coming out true. */
    private static Generator.BoundaryAttempt composedPast(int i) {
        Reachability reached = Reachability.of(new WayToTheBorder(stated(i)), declarations());
        assertTrue(reached instanceof Reachability.Reaching,
                () -> "the way is open: " + SHAPES.get(i).written());
        Axis gate = axes().stream().filter(each -> each.path().toString().equals("x.gate"))
                .findFirst().orElseThrow();
        return Generator.probeFixing(subject(), "x.gate = 1",
                Map.of(new RealizationTarget.AtOnePosition(gate.term()), Count.of(1)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain("decide").quantities(rules()).ordersOf(gate.term()).answered(),
                        Count.of(1)))),
                (Reachability.Reaching) reached, Generator.CandidateCheck.ANY);
    }

    /** What shape {@code i} coming out true asks of a row, as conditions on the way. */
    private static List<OnTheWay> stated(int i) {
        String behavior = "s" + i;
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputDomain inputs = domain(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules()), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        InputReading reading = inputs.reading(rules());
        return ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior,
                                ConditionOccurrence.Reading.DIVIDING)),
                reading, true, WhatConditionsState.of(reading)).entries();
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

    private static SearchRegion declarations() {
        return domain("decide").quantities(rules()).region();
    }

    private static List<Axis> axes() {
        return COMPILATION.db().ask(new Adequacy.Divided(module(), "decide")).value().axes();
    }

    private static MeasuredInput subject() {
        return MeasuredInput.of("decide", domain("decide").reading(rules()),
                AxesATestWrote.asAMeasurement("decide", axes()));
    }
}
