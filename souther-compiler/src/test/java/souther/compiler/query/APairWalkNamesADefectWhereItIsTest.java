package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the pair walk says, asked of the walk itself rather than through a compile.
 *
 * <p>{@link EverythingAnAnswerHoldsMeansSomethingTest} keeps a register of what an answer holds that
 * cannot compare as a value, and that register is worth what the walk under it is worth. A walk that
 * names the holder of a defect instead of the defect puts the wrong line in the register; one that
 * files a container comparing by address as a compile that did not reproduce puts it under the wrong
 * heading; one that stops early and says nothing agrees with the register about less than the
 * register names. None of those can be seen from a corpus, where the answer is whatever the compiler
 * happens to hold.
 *
 * <p>So the shapes are built here. Each is the smallest object graph that has the property, and each
 * assertion is about what the walk answers and not about what a compiler does.
 */
class APairWalkNamesADefectWhereItIsTest {

    /** Something that says which object it is and nothing else, which is what a walk is looking
     *  for. */
    private static final class Address {}

    /** A record whose equality rests on one of those, so it is unequal to its own twin. */
    private record Point(Address held) {}

    /** And two ways down to one of those. */
    private record Holder(Point point) {}

    private record Root(Holder one, Holder two) {}

    private static Set<String> found(Divergence.Walked walked) {
        Set<String> out = new LinkedHashSet<>();
        walked.found().forEach(each ->
                out.add(each.at() + " " + each.cause() + " " + each.kind()));
        return out;
    }

    /**
     * A thing two paths reach is named at both, and neither path's holder is named for it.
     *
     * <p>The walk remembers pairs so a graph that shares is walked once, and what it remembers has to
     * be what the first walk found rather than the fact of having been there. Remembering only that,
     * the second path comes back with nothing — and whoever holds it, being unequal itself and having
     * found nothing below, is named for a defect several levels under it.
     */
    @Test
    void aThingTwoPathsReachIsNamedAtBoth() {
        Address mine = new Address();
        Address theirs = new Address();
        Point one = new Point(mine);
        Point other = new Point(theirs);
        // One Point under two Holders, which is what makes the second path a second occurrence of
        // one pair rather than a pair of its own.
        Root left = new Root(new Holder(one), new Holder(one));
        Root right = new Root(new Holder(other), new Holder(other));

        Divergence.Walked walked = Divergence.between(left, right);

        assertEquals(Set.of(".Root#one.Holder#point.Point#held " + Address.class.getName() + " THE_SAME_THING_TWICE",
                        ".Root#two.Holder#point.Point#held " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked),
                "the thing that cannot compare, named at each path that holds it");
        assertTrue(walked.traversal().complete(),
                () -> "nothing stopped this walk: " + walked.traversal().interruptions());
    }

    /**
     * A container comparing its members by address is the same thing said twice.
     *
     * <p>Its own equality is no help and neither is its key set: both answer by address, so both say
     * no however equal the members are. Read as an answer, that no is a compile that did not
     * reproduce — a fault of a different kind, which no equality can fix and which sends whoever
     * reads it after the compiler instead of after the container.
     *
     * <p>So the correspondence is built from what the keys themselves say. Paired that way the two
     * are walked like any other map, come back with nothing under them, and are named for what they
     * are.
     */
    @Test
    void aMapThatComparesItsKeysByAddressIsNotTwoDifferentAnswers() {
        Map<Object, Object> left = new IdentityHashMap<>();
        Map<Object, Object> right = new IdentityHashMap<>();
        // Keys that mean the same and are two objects, which is every key of one of these across two
        // stores.
        left.put(new String("k"), "v");
        right.put(new String("k"), "v");

        Divergence.Walked walked = Divergence.between(left, right);

        assertEquals(Set.of(" java.util.IdentityHashMap THE_SAME_THING_TWICE"), found(walked),
                "a map comparing by address, said as what it is");
        assertTrue(walked.traversal().complete(),
                () -> "nothing stopped this walk: " + walked.traversal().interruptions());
    }

    /** And a map that holds different things still says so, which is what the above must not take
     *  away. */
    @Test
    void andAMapHoldingSomethingElseStillSaysSo() {
        Divergence.Walked walked = Divergence.between(
                new HashMap<>(Map.of("k", "v")), new HashMap<>(Map.of("k", "w")));

        assertEquals(Set.of("{value} java.lang.String DIFFERENT_THINGS"), found(walked),
                "one input answered differently, which is not about equality");
    }

    /**
     * What an absence holds is walked, and the absence is not named for it.
     *
     * <p>The field inside one of these belongs to {@code java.base}, which opens nothing to a walk
     * from here — so a pair of them taken apart by their fields is a pair nothing can get inside, and
     * everything an answer keeps behind one goes unasked. Read through instead, what is in there is
     * reached and named where it sits.
     */
    @Test
    void whatAnAbsenceHoldsIsWalked() {
        Divergence.Walked walked = Divergence.between(
                java.util.Optional.of(new Address()), java.util.Optional.of(new Address()));

        assertEquals(Set.of("? " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "what is inside, named inside");
        assertTrue(walked.traversal().complete(),
                () -> "and nothing stopped the walk: " + walked.traversal().interruptions());
    }

    /** And an absence against a thing is two different answers, which is not about equality. */
    @Test
    void andAnAbsenceAgainstAThingIsADifferentAnswer() {
        Divergence.Walked walked = Divergence.between(
                java.util.Optional.empty(), java.util.Optional.of("v"));

        assertEquals(Set.of(" java.util.Optional DIFFERENT_THINGS"), found(walked),
                "one held something and the other did not");
    }

    /** A record that calls one of its components what a map calls its far side. */
    private record Holding(Address value) {}

    /**
     * A component called {@code value} and the value side of a map are two places.
     *
     * <p>Which is what the steps are kept for. Written as text on the way down, both come out
     * {@code .value} and a register keyed by where something sits would hold one line for two
     * places — and a reader of it could not tell which of them to go and look at.
     */
    @Test
    void aComponentCalledValueIsNotTheValueSideOfAMap() {
        Set<String> underAComponent = found(Divergence.between(
                new Holding(new Address()), new Holding(new Address())));
        Set<String> underAMap = found(Divergence.between(
                new HashMap<>(Map.of("k", new Address())),
                new HashMap<>(Map.of("k", new Address()))));

        assertEquals(Set.of(".Holding#value " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                underAComponent, "a component the record calls value");
        assertEquals(Set.of("{value} " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                underAMap, "and the far side of an entry, which is not that");
    }

    /**
     * Two sets holding the same things in different orders are not two different answers.
     *
     * <p>What pairs two containers is their own contract, and a set is equal to another by what is
     * in it. Paired by the order an iterator gives, these two come back as members that differ —
     * this saying one input compiled to two different answers, about two values the language calls
     * equal.
     */
    @Test
    void twoSetsHoldingTheSameThingsAreNotTwoAnswers() {
        java.util.Set<String> left = new java.util.LinkedHashSet<>(List.of("a", "b"));
        java.util.Set<String> right = new java.util.LinkedHashSet<>(List.of("b", "a"));

        Divergence.Walked walked = Divergence.between(
                new Holds(left, new Address()), new Holds(right, new Address()));

        assertEquals(Set.of(".Holds#beside " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "the sets hold the same things, and only what is beside them differs");
        assertTrue(walked.traversal().complete(),
                () -> "and nothing stopped the walk: " + walked.traversal().interruptions());
    }

    /**
     * Something to hold a container in, beside something that never compares.
     *
     * <p>Both halves. Held on its own, two of these are equal wherever the containers are, and the
     * walk stops at them without ever reaching what is inside — so the container's own rule would go
     * untested and the assertion would pass on a walk that never happened.
     */
    private record Holds(Object it, Address beside) {}

    /** And a list is still paired by position, which is what a list's equality is. */
    @Test
    void aListIsPairedByPosition() {
        Address beside = new Address();
        Divergence.Walked walked = Divergence.between(
                new Holds(List.of("a", "b"), beside), new Holds(List.of("b", "a"), beside));

        assertEquals(Set.of(".Holds#it[] java.lang.String DIFFERENT_THINGS"), found(walked),
                "two lists holding the same things in two orders are two lists");
    }

    /** A collection that is neither is where the walk stops rather than guesses. */
    @Test
    void aCollectionThatIsNeitherAListNorASetStopsTheWalk() {
        Address beside = new Address();
        Divergence.Walked walked = Divergence.between(
                new Holds(new java.util.ArrayDeque<>(List.of("a")), beside),
                new Holds(new java.util.ArrayDeque<>(List.of("a")), beside));

        assertFalse(walked.traversal().complete(), "neither position nor membership is its equality");
        assertEquals(Set.of("A_CONTAINER_WITH_NO_RULE_FOR_PAIRING .Holds#it"),
                walked.traversal().interruptions().stream()
                        .map(each -> each.why() + " " + each.at())
                        .collect(java.util.stream.Collectors.toSet()),
                "said as what it is");
    }

    /** Something whose insides belong to a module that opens nothing here. */
    private record Dated(java.time.LocalDateTime at) {}

    /**
     * A field the runtime will not hand over is said out loud.
     *
     * <p>What is under it was never compared. Swallowed, a walk that could not get into half of two
     * answers would agree with a register as readily as one that read all of them.
     */
    @Test
    void aFieldThatWouldNotOpenStopsTheWalk() {
        Divergence.Walked walked = Divergence.between(
                new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)),
                new Dated(java.time.LocalDateTime.of(2026, 1, 2, 0, 0)));

        assertFalse(walked.traversal().complete(), "java.base opens nothing to this");
        assertTrue(walked.traversal().interruptions().stream().anyMatch(each ->
                        each.why() == Divergence.Interruption.Why.A_FIELD_THAT_WOULD_NOT_OPEN),
                () -> "for the reason it is: " + walked.traversal().interruptions());
    }

    /**
     * And a walk that runs out of its bound says that rather than stopping quietly.
     *
     * <p>The bound is what keeps a graph nobody meant to walk from being walked, and a compile is
     * given more of it than anything here reaches — so the path out of it would rot unread, and the
     * arm that reports it would go with it. Held by giving one walk almost none.
     */
    @Test
    void aWalkThatRunsOutOfItsBoundSaysSo() {
        Divergence.Walked walked = Divergence.between(
                new Root(new Holder(new Point(new Address())), new Holder(new Point(new Address()))),
                new Root(new Holder(new Point(new Address())), new Holder(new Point(new Address()))),
                1);

        assertFalse(walked.traversal().complete(), "one pair is not the whole of that graph");
        assertTrue(walked.traversal().interruptions().stream().anyMatch(each ->
                        each.why() == Divergence.Interruption.Why.BUDGET_EXHAUSTED),
                () -> "for the reason it is: " + walked.traversal().interruptions());
    }

    /**
     * And every way this walk can stop is one of these.
     *
     * <p>The arms are the checklist. A walk that reports nothing over a corpus says only that
     * nothing happened there today, so a path out that no shape here reaches is a path that could
     * stop reporting without anything going red — and an arm added to the mechanism arrives with
     * nobody having built the graph that reaches it.
     */
    @Test
    void everyWayThisWalkCanStopIsBuiltHere() {
        Set<Divergence.Interruption.Why> met = new java.util.LinkedHashSet<>();
        stoppedWalks().forEach(walked -> walked.traversal().interruptions()
                .forEach(each -> met.add(each.why())));

        assertEquals(java.util.EnumSet.allOf(Divergence.Interruption.Why.class),
                java.util.EnumSet.copyOf(met),
                "a way this walk can stop that no graph here reaches");
    }

    /** Every graph above that stops the walk, in one place, so the arms can be counted. */
    private static List<Divergence.Walked> stoppedWalks() {
        Address beside = new Address();
        Map<Object, Object> unpairable = new HashMap<>();
        unpairable.put(new Address(), "v");
        Map<Object, Object> alsoUnpairable = new HashMap<>();
        alsoUnpairable.put(new Address(), "v");
        // The loop is made of something with no equality of its own. A container that holds itself
        // has an `equals` that never comes back, and asking it is what a walk of two of them does
        // before it descends — the graph would take the stack rather than the arm under test.
        Loop ring = new Loop();
        ring.again = ring;
        Loop alsoRing = new Loop();
        alsoRing.again = alsoRing;
        return List.of(
                Divergence.between(unpairable, alsoUnpairable),
                Divergence.between(ring, alsoRing),
                Divergence.between(new Holds(new java.util.ArrayDeque<>(List.of("a")), beside),
                        new Holds(new java.util.ArrayDeque<>(List.of("a")), beside)),
                Divergence.between(new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)),
                        new Dated(java.time.LocalDateTime.of(2026, 1, 2, 0, 0))),
                Divergence.between(new Holder(new Point(new Address())),
                        new Holder(new Point(new Address())), 1));
    }

    /**
     * A map whose keys mean the same and are not the same is where the walk stops.
     *
     * <p>A correspondence built by putting one side into a map of its own keys loses a key wherever
     * two of them say the same thing — which is what a map comparing its keys by address is for. The
     * side that survived then pairs with everything, every entry looks accounted for, and what was
     * never compared is what the collapse took away.
     */
    @Test
    void aMapHoldingTwoKeysThatMeanOneThingStopsTheWalk() {
        Map<Object, Object> left = new IdentityHashMap<>();
        left.put(new String("k"), "v");
        left.put(new String("k"), "w");
        Map<Object, Object> right = new IdentityHashMap<>();
        right.put(new String("k"), "v");
        right.put(new String("k"), "w");

        Divergence.Walked walked = Divergence.between(left, right);

        assertFalse(walked.traversal().complete(), "two keys of one meaning is not a correspondence");
        assertEquals(Set.of("MEMBERS_THAT_DO_NOT_PAIR {key}"),
                walked.traversal().interruptions().stream()
                        .map(each -> each.why() + " " + each.at())
                        .collect(java.util.stream.Collectors.toSet()),
                "said as somewhere the walk could not go");
    }

    /** Two maps of one size whose keys line up with nothing. */
    @Test
    void twoMapsWhoseKeysDoNotPairAreWhereTheWalkStops() {
        Map<Object, Object> left = new HashMap<>();
        Map<Object, Object> right = new HashMap<>();
        left.put(new Address(), "v");
        right.put(new Address(), "v");

        Divergence.Walked walked = Divergence.between(left, right);

        assertFalse(walked.traversal().complete(), "the entries line up with nothing");
        assertEquals(Set.of("MEMBERS_THAT_DO_NOT_PAIR {key}"),
                walked.traversal().interruptions().stream()
                        .map(each -> each.why() + " " + each.at())
                        .collect(java.util.stream.Collectors.toSet()),
                "said as a place the walk could not go, and not as a verdict on which it is");
        assertEquals(Set.of(), found(walked),
                "and nothing is guessed about it");
    }

    /** Something whose only field is itself, so a walk of it finds nothing and gets nowhere. */
    private static final class Loop {
        private Loop again;
    }

    /**
     * A graph that holds itself stops the walk, and nothing is named for what was not looked at.
     *
     * <p>The pair on the way down has nothing to report yet, so a descent that meets it has not
     * settled what is under it. What names a thing for itself is finding nothing under it, and that
     * rule only holds where the looking finished — read off a descent that stopped, it names whatever
     * the walk gave up inside.
     */
    @Test
    void aGraphThatHoldsItselfStopsTheWalk() {
        Loop left = new Loop();
        left.again = left;
        Loop right = new Loop();
        right.again = right;

        Divergence.Walked walked = Divergence.between(left, right);

        assertFalse(walked.traversal().complete(), "the walk met the pair it was already walking");
        assertEquals(Set.of("A_GRAPH_THAT_LOOPS .Loop#again"),
                walked.traversal().interruptions().stream()
                        .map(each -> each.why() + " " + each.at())
                        .collect(java.util.stream.Collectors.toSet()),
                "for the reason it is, and where");
        assertEquals(Set.of(), found(walked),
                "and nothing is named for what the walk did not get to");
    }
}
