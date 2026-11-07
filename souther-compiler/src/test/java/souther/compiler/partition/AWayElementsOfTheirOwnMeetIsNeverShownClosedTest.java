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
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
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
 * group — each asking its item one of one or two ways of one or two bounds, against a written
 * number or against the group's own {@code m}, which the body may bound as well, as it may the
 * number of items. Whether some input meets one is worked out by running it over every group of
 * at most two items, with every {@code m}, of the values the bounds tell apart, which is every way
 * a group can meet a body of at most two quantifiers asking some item. Where some group meets it,
 * neither the way to it nor a row composed past it is said to be closed. Where it asks some item
 * of one quantifier, or of each, beside what every item meets one of, what no group meets, the way
 * is closed: what one quantifier asks is one item's, and what every item meets and what the group
 * is asked hold of it.
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

    /**
     * A quantifier over the items: every item or some item meets one of {@code ways}, each of
     * which is every one of its bounds.
     */
    private record Quantifier(boolean every, List<List<Bound>> ways) {

        /** One way of {@code bounds}. */
        static Quantifier of(boolean every, List<Bound> bounds) {
            return new Quantifier(every, List.of(bounds));
        }

        boolean holds(List<Integer> items, int m) {
            return every ? items.stream().allMatch(n -> meets(n, m))
                    : items.stream().anyMatch(n -> meets(n, m));
        }

        private boolean meets(int n, int m) {
            return ways.stream().anyMatch(way -> way.stream().allMatch(bound -> bound.holds(n, m)));
        }

        String written(String item, String container) {
            return "List." + (every ? "all" : "any") + "(" + item + " -> " + ways.stream()
                    .map(way -> way.stream().map(bound -> bound.written(item + ".n"))
                            .collect(Collectors.joining(" && ", ways.size() > 1 ? "(" : "",
                                    ways.size() > 1 ? ")" : "")))
                    .collect(Collectors.joining(" || ")) + ", " + container + ")";
        }
    }

    /**
     * Quantifiers over the items of a group, or of a sub of a group where {@code deeper}, all of
     * which some group of the input meets together, beside the bounds {@code onTheGroup} asks of
     * its {@code m} and, where {@code twoItems}, the items being two at least.
     */
    private record Shape(boolean deeper, List<Bound> onTheGroup, List<Quantifier> quantifiers,
                         boolean twoItems) {

        Shape(boolean deeper, List<Bound> onTheGroup, List<Quantifier> quantifiers) {
            this(deeper, onTheGroup, quantifiers, false);
        }

        /** Whether some input meets it: some group, or some sub of one, whose items meet all. */
        boolean met() {
            return VALUES.stream().anyMatch(m ->
                    onTheGroup.stream().allMatch(bound -> bound.holds(m, m))
                    && ITEMS.stream().anyMatch(items -> (!twoItems || items.size() >= 2)
                            && quantifiers.stream().allMatch(each -> each.holds(items, m))));
        }

        /**
         * Whether what it asks of the items is what this compiler answers exactly: one quantifier
         * asking some item one way; or, where the items are two at least, what every item meets
         * one of several ways beside quantifiers each asking some item one way.
         *
         * <p>Not two statements of every item, which are asked apart and so less than together;
         * nor one way every item meets beside some item, where the items may also be none: the
         * container holding none is a way of its own, which what some item is asked does not
         * close.
         */
        boolean askedExactly() {
            if (quantifiers.size() == 1 && !quantifiers.getFirst().every()
                    && quantifiers.getFirst().ways().size() == 1) {
                return true;
            }
            return twoItems
                    && quantifiers.stream().filter(each -> each.every()
                            && each.ways().size() > 1).count() == 1
                    && quantifiers.stream().allMatch(each -> each.every()
                            || each.ways().size() == 1);
        }

        /** Each part of the body a level in, as a shape of its own. */
        List<Shape> parts() {
            List<Shape> out = new ArrayList<>();
            onTheGroup.forEach(bound -> out.add(new Shape(false, List.of(bound), List.of())));
            if (twoItems) {
                out.add(new Shape(false, List.of(), List.of(), true));
            }
            quantifiers.forEach(each -> out.add(new Shape(false, List.of(), List.of(each))));
            return out;
        }

        String written() {
            String holder = deeper ? "s" : "g";
            List<String> parts = new ArrayList<>();
            onTheGroup.forEach(bound -> parts.add(bound.written("g.m")));
            if (twoItems) {
                parts.add("List.length(" + holder + ".items) >= 2");
            }
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
     * Every item meeting one of two ways, each a bound against a written number and one against
     * the group's number: every two of the four such ways, which some group's number leaves no
     * item meeting either of.
     */
    private static final List<Quantifier> EACH_ONE_OF_TWO_AGAINST_THE_GROUP = eachOneOfTwo();

    private static List<Quantifier> eachOneOfTwo() {
        List<List<Bound>> ways = new ArrayList<>();
        for (Bound written : List.of(new Bound(true, 0, false), new Bound(false, 1, false))) {
            for (Bound ofTheGroup : List.of(new Bound(true, 0, true),
                    new Bound(false, 0, true))) {
                ways.add(List.of(written, ofTheGroup));
            }
        }
        List<Quantifier> out = new ArrayList<>();
        for (List<List<Bound>> two : twoOf(ways)) {
            if (!two.getFirst().equals(two.getLast())) {
                out.add(new Quantifier(true, two));
            }
        }
        return List.copyOf(out);
    }

    /**
     * One quantifier of either kind asking two bounds, and two quantifiers of either kind asking
     * one each; with a bound on the group's number, one quantifier of some item or two asking
     * bounds against it; every item meeting one of two bounds beside no, one or two quantifiers
     * of some item asking one bound, or one asking two, the items two at least or not — a level in
     * and two levels in; and a level in, with two
     * bounds on the group's number, every item meeting one of two ways against it, the items two
     * at least or not.
     *
     * <p>Each two once, in one order: the parts of a conjunction and of a disjunction are read in
     * the order of their spellings, so the other order is the same statement read again.
     */
    private static final List<Shape> SHAPES = shapes();

    private static List<Shape> shapes() {
        List<Quantifier> ofOne = new ArrayList<>();
        for (boolean every : List.of(false, true)) {
            BOUNDS.forEach(bound -> ofOne.add(Quantifier.of(every, List.of(bound))));
        }
        List<Quantifier> someOfOne = ofOne.stream().filter(each -> !each.every()).toList();
        List<List<Quantifier>> beside = new ArrayList<>();
        beside.add(List.of());
        someOfOne.forEach(each -> beside.add(List.of(each)));
        beside.addAll(twoOf(someOfOne));
        twoOf(BOUNDS).forEach(two -> beside.add(List.of(Quantifier.of(false, two))));
        List<Shape> out = new ArrayList<>();
        for (boolean deeper : List.of(false, true)) {
            for (boolean every : List.of(false, true)) {
                for (List<Bound> two : twoOf(BOUNDS)) {
                    out.add(new Shape(deeper, List.of(), List.of(Quantifier.of(every, two))));
                }
            }
            for (List<Quantifier> two : twoOf(ofOne)) {
                out.add(new Shape(deeper, List.of(), two));
            }
            for (Bound group : BOUNDS) {
                for (List<Bound> two : twoOf(AGAINST_THE_GROUP)) {
                    out.add(new Shape(deeper, List.of(group),
                            List.of(Quantifier.of(false, two))));
                    out.add(new Shape(deeper, List.of(group), List.of(
                            Quantifier.of(false, List.of(two.getFirst())),
                            Quantifier.of(false, List.of(two.getLast())))));
                }
            }
            for (List<Bound> two : twoOf(BOUNDS)) {
                if (two.getFirst().equals(two.getLast())) {
                    continue;
                }
                Quantifier eachOneOfTwo = new Quantifier(true,
                        List.of(List.of(two.getFirst()), List.of(two.getLast())));
                for (List<Quantifier> some : beside) {
                    List<Quantifier> asked = new ArrayList<>(some);
                    asked.addFirst(eachOneOfTwo);
                    for (boolean twoItems : List.of(false, true)) {
                        out.add(new Shape(deeper, List.of(), asked, twoItems));
                    }
                }
            }
        }
        for (List<Bound> group : twoOf(BOUNDS)) {
            for (Quantifier every : EACH_ONE_OF_TWO_AGAINST_THE_GROUP) {
                for (boolean twoItems : List.of(false, true)) {
                    out.add(new Shape(false, group, List.of(every), twoItems));
                }
            }
        }
        return List.copyOf(out);
    }

    /** Every two of {@code these}, each two once and one of them twice. */
    private static <T> List<List<T>> twoOf(List<T> these) {
        List<List<T>> out = new ArrayList<>();
        for (int i = 0; i < these.size(); i++) {
            for (int j = i; j < these.size(); j++) {
                out.add(List.of(these.get(i), these.get(j)));
            }
        }
        return out;
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
    void aWayNoGroupMeetsWhereItIsAskedExactlyIsClosed() {
        List<String> open = new ArrayList<>();
        int asked = 0;
        boolean everyItemAsked = false;
        for (int i = 0; i < SHAPES.size(); i++) {
            Shape shape = SHAPES.get(i);
            if (!shape.askedExactly() || shape.met()) {
                continue;
            }
            asked++;
            everyItemAsked |= shape.twoItems();
            if (Reachability.of(new WayToTheBorder(stated(i)), declarations())
                    instanceof Reachability.Reaching) {
                open.add(shape.written());
            }
        }
        assertTrue(asked > 0 && everyItemAsked,
                "some shape of each kind asks what no group meets");
        assertEquals(List.of(), open, "no group meets what each of these asks");
    }

    /**
     * What is left of an element turns on what it was asked and not on the order: what each part
     * of a shape's body asks a group, one choice of each, taken in one by one from the first or
     * from the last, leaves nothing exactly where it all taken in at once does.
     *
     * <p>What the parts ask is read part by part, each as a shape of its own, so it is what a walk
     * of the body takes in and not what the walk kept: a body no group meets asks, part by part,
     * what leaves nothing. A walk takes the parts in the order of their spellings, which is one
     * order; the others are asked here.
     */
    @Test
    void whatIsLeftOfAnElementDoesNotTurnOnTheOrderItIsAskedIn() {
        WhatAnElementIsLeft nothingAsked = WhatAnElementIsLeft.of(declarations());
        List<String> differ = new ArrayList<>();
        int leaveNone = 0;
        for (Shape shape : SHAPES) {
            Optional<List<List<RowDemand.AskedOfAnElement>>> asked = askedPartByPart(shape);
            if (asked.isEmpty()) {
                continue;
            }
            for (List<RowDemand.AskedOfAnElement> each : asked.get()) {
                boolean together = nothingAsked.with(each).isEmpty();
                if (together) {
                    leaveNone++;
                }
                for (List<RowDemand.AskedOfAnElement> order : List.of(each, each.reversed())) {
                    Optional<WhatAnElementIsLeft> left = Optional.of(nothingAsked);
                    for (RowDemand.AskedOfAnElement one : order) {
                        left = left.flatMap(so -> so.with(List.of(one)));
                    }
                    if (left.isEmpty() != together) {
                        differ.add(shape.written() + " taken in as " + order);
                    }
                }
            }
        }
        assertTrue(leaveNone > 0, "some shape asks what leaves no group");
        assertEquals(List.of(), differ, "taken in one by one");
    }

    /**
     * What {@code shape}'s parts ask a group, one choice of each, every way: each part read as a
     * shape of its own. Nothing where some part is read as no demand on a group, or the shape is
     * a level further in, where what is asked of a group is asked of a sub of it.
     */
    private static Optional<List<List<RowDemand.AskedOfAnElement>>> askedPartByPart(Shape shape) {
        if (shape.deeper()) {
            return Optional.empty();
        }
        List<List<RowDemand.AskedOfAnElement>> out = List.of(List.of());
        for (Shape part : shape.parts()) {
            if (!(stated(part).getFirst()
                    instanceof OnTheWay.TakenIn(var _, RowDemand.Exists some, var _, var _))) {
                return Optional.empty();
            }
            List<List<RowDemand.AskedOfAnElement>> joined = new ArrayList<>();
            for (List<RowDemand.AskedOfAnElement> before : out) {
                for (List<RowDemand.AskedOfAnElement> way : some.ofAnElement().asAsked()) {
                    List<RowDemand.AskedOfAnElement> both = new ArrayList<>(before);
                    both.addAll(way);
                    joined.add(List.copyOf(both));
                }
            }
            out = joined;
        }
        return Optional.of(out);
    }

    /**
     * And past a guard some group meets, a comparison on another number draws the lines it draws
     * past any other guard some group meets: what the guard asks of the items is about none of
     * that number's values. Held for the guard of two quantifiers of some item over one group's
     * items, and for every item meeting one of two ways beside them, against a guard of one.
     */
    @Test
    void aLineOnAnotherNumberPastAGuardSomeGroupMeetsIsTheLineItDrawsPastAnyOther() {
        String asked = "List.any(g -> List.any(a -> a.n < 0, g.items), x.groups)";
        List<String> drawn = gateLinesPast(asked);
        assertTrue(!drawn.isEmpty(), () -> "a line is drawn on x.gate past " + asked);
        for (String guard : List.of(
                "List.any(g -> List.any(a -> a.n < 0, g.items)"
                        + " && List.any(b -> b.n >= 1, g.items), x.groups)",
                "List.any(g -> List.length(g.items) >= 2"
                        + " && List.all(i -> i.n < 0 || i.n >= 1, g.items)"
                        + " && List.any(a -> a.n < 0, g.items)"
                        + " && List.any(b -> b.n >= 1, g.items), x.groups)")) {
            assertEquals(drawn, gateLinesPast(guard), guard);
        }
    }

    /**
     * What a composer is handed of every item meeting one of several ways is held to the figure
     * the ways of an element are: every choice of a way for each such statement is a way a row
     * written alike meets, and past the figure the rest are said to be left unread rather than
     * made.
     */
    @Test
    void theWaysEveryItemMeetingOneOfSeveralIsWrittenInAreHeldToTheFigure() {
        List<String> eachOneOfTwo = List.of("i.n < 0 || i.n >= 1", "i.n < 0 || i.n >= 2",
                "i.n < -1 || i.n >= 1", "i.n < -1 || i.n >= 2", "i.n < 1 || i.n >= 2",
                "i.n < -2 || i.n >= 0");
        String body = eachOneOfTwo.stream().map(each -> "List.all(i -> " + each + ", g.items)")
                .collect(Collectors.joining(" && "));
        Compilation made = Compilation.ofSource("""
                module probe.figure

                data Item = { n: Int }
                    invariant n >= -10 && n <= 10
                data Group = { items: List<Item> }
                data Input = { groups: List<Group> }

                behavior many : (x: Input) -> Bool
                let many (x) = List.any(g -> %s, x.groups)
                """.formatted(body), "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        List<OnTheWay> stated = statedIn(made, "many");
        List<Integer> handed = new ArrayList<>();
        List<WhyNotTaken> declined = new ArrayList<>();
        stated.forEach(each -> collect(each, handed, declined));
        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertTrue(handed.stream().allMatch(ways -> ways <= most),
                () -> "no demand hands a composer more ways than the figure: " + handed);
        assertTrue(declined.stream().anyMatch(WhyNotTaken.MoreWaysThanAreRead.class::isInstance),
                () -> "and the rest are said to be unread: " + declined);
    }

    /** The ways each demand on an element hands a composer, and every reason something on the
     *  way was declined, in {@code entry} and every alternative of it. */
    private static void collect(OnTheWay entry, List<Integer> handed, List<WhyNotTaken> declined) {
        switch (entry) {
            case OnTheWay.TakenIn(var _, RowDemand.Exists some, var _, var _) ->
                    handed.add(some.ofAnElement().ways().size());
            case OnTheWay.TakenIn(var _, RowDemand.ForAll every, var _, var _) ->
                    handed.add(every.ofEachElement().ways().size());
            case OnTheWay.Declined declinedHere -> declined.addAll(declinedHere.whys());
            default -> entry.alternatives().forEach(alternative ->
                    alternative.forEach(each -> collect(each, handed, declined)));
        }
    }

    /** What {@code behavior}'s body asks of a row coming out true, read in {@code made}. */
    private static List<OnTheWay> statedIn(Compilation made, String behavior) {
        String module = made.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(made, module);
        AnalysisBody analysis = made.db().ask(new Bodies.Checked(module)).value()
                .analysisBodies().get(behavior);
        InputDomain inputs = made.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        InputReading reading = inputs.reading(rules);
        return ReachingCuts.stating(Condition.of(analysis.core(), reads, rules.symbols(),
                        rules.newtypes(), new ConditionNumbering(module, behavior,
                                ConditionOccurrence.Reading.DIVIDING)),
                reading, true, WhatConditionsState.of(reading)).entries();
    }

    /** The lines drawn on {@code x.gate} past {@code guard}, each as what it is on and the points
     *  a row is asked to stand at. */
    private static List<String> gateLinesPast(String guard) {
        Compilation made = Compilation.ofSource("""
                module probe.pastaguard

                data Item = { n: Int }
                    invariant n >= -10 && n <= 10
                data Group = { items: List<Item> }
                data Input = { groups: List<Group>, gate: Int }
                    invariant gate >= -10 && gate <= 10
                data A
                data B
                data C

                behavior f : (x: Input) -> A | B | C
                let f (x) = {
                    guard %s else C
                    if x.gate > 0 then A else B
                }
                """.formatted(guard), "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        List<BorderAssessment> lines = Adequacy.readingsOf(made.db(), "probe.pastaguard").get("f");
        assertNotNull(lines, "f was measured");
        return lines.stream().map(line -> line.border().cut() + " " + new TreeSet<>(
                        line.items().keySet().stream().map(String::valueOf).toList()))
                .filter(line -> line.contains("x.gate")).sorted().toList();
    }

    /** Every shape asked of, and each part of one a level in as a shape of its own. */
    private static final List<Shape> READ = read();

    private static List<Shape> read() {
        Set<Shape> out = new LinkedHashSet<>(SHAPES);
        SHAPES.stream().filter(shape -> !shape.deeper())
                .forEach(shape -> out.addAll(shape.parts()));
        return List.copyOf(out);
    }

    /** The input every shape and the behavior a row is composed for read. */
    private static final String DECLARED = """
            data Item = { n: Int }
                invariant n >= -10 && n <= 10

            data Sub = { items: List<Item> }

            data Group = { items: List<Item>, subs: List<Sub>, m: Int }

            data Input = { groups: List<Group>, gate: Int }
                invariant gate >= -10 && gate <= 10
            """;

    private static final String MODEL = "module probe.ownelements\n\n" + DECLARED + "\n"
            + IntStream.range(0, READ.size())
            .mapToObj(i -> "behavior s" + i + " : (x: Input) -> Bool\nlet s" + i + " (x) = "
                    + READ.get(i).written())
            .collect(Collectors.joining("\n\n"));

    /**
     * The behavior a row past a shape is composed for, compiled apart from the shapes: what it
     * is measured by is worked out over every behavior of its module, and the shapes are many.
     */
    private static final String DECIDING = "module probe.deciding\n\n" + DECLARED + """

            data A
            data B

            behavior decide : (x: Input) -> A | B
            let decide (x) = if x.gate > 0 then A else B
            """;

    private static final Compilation COMPILATION = compiled(MODEL);

    private static final Compilation DECIDE = compiled(DECIDING);

    /** Compiled and asked nothing more: what each test asks of it is read when it is asked. */
    private static Compilation compiled(String model) {
        Compilation made = Compilation.ofSource(model, "Main");
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
                        deciding().quantities(decidingRules()).ordersOf(gate.term()).answered(),
                        Count.of(1)))),
                (Reachability.Reaching) reached, Generator.CandidateCheck.ANY);
    }

    /** What each shape coming out true asks of a row, read once for every test that asks it. */
    private static final Map<Shape, List<OnTheWay>> STATED = new ConcurrentHashMap<>();

    /** What shape {@code i} coming out true asks of a row, as conditions on the way. */
    private static List<OnTheWay> stated(int i) {
        return stated(SHAPES.get(i));
    }

    /** What {@code shape} coming out true asks of a row, as conditions on the way. */
    private static List<OnTheWay> stated(Shape shape) {
        return STATED.computeIfAbsent(shape,
                AWayElementsOfTheirOwnMeetIsNeverShownClosedTest::readOf);
    }

    private static List<OnTheWay> readOf(Shape shape) {
        String behavior = "s" + READ.indexOf(shape);
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

    /** What the declarations of the input leave, as the behavior a row is composed for reads it. */
    private static SearchRegion declarations() {
        return deciding().quantities(decidingRules()).region();
    }

    private static InputDomain deciding() {
        InputDomain read = DECIDE.db().ask(new Adequacy.Inputs(decidingModule())).value()
                .get("decide");
        assertNotNull(read, "the behavior a row is composed for compiles");
        return read;
    }

    private static String decidingModule() {
        return DECIDE.modules().getFirst();
    }

    private static RuleReadingSource decidingRules() {
        return RuleReadings.of(DECIDE, decidingModule());
    }

    private static List<Axis> axes() {
        return DECIDE.db().ask(new Adequacy.Divided(decidingModule(), "decide")).value().axes();
    }

    private static MeasuredInput subject() {
        return MeasuredInput.of("decide", deciding().reading(decidingRules()),
                AxesATestWrote.asAMeasurement("decide", axes()));
    }
}
