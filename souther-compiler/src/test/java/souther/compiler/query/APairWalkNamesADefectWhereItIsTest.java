package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    /** What a walk found, whether or not it got to the end of what it was walking. */
    private static Set<String> found(Covered<Divergence> covered) {
        List<Divergence> each = switch (covered) {
            case Covered.Whole<Divergence>(List<Divergence> all) -> all;
            case Covered.Partly<Divergence>(List<Divergence> all, List<Gap> _) -> all;
        };
        Set<String> out = new LinkedHashSet<>();
        each.forEach(one -> out.add(one.at() + " " + one.cause() + " " + one.kind()));
        return out;
    }

    /** And where it fell short, which is empty exactly where it did not. */
    private static Set<String> gaps(Covered<Divergence> covered) {
        return switch (covered) {
            case Covered.Whole<Divergence> _ -> Set.of();
            case Covered.Partly<Divergence>(List<Divergence> _, List<Gap> gaps) -> {
                Set<String> out = new java.util.TreeSet<>();
                gaps.forEach(gap -> out.add(gap.toString()));
                yield out;
            }
        };
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

        Covered<Divergence> walked = Divergence.between(left, right);

        assertEquals(Set.of(".Root#one.Holder#point.Point#held " + Address.class.getName() + " THE_SAME_THING_TWICE",
                        ".Root#two.Holder#point.Point#held " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked),
                "the thing that cannot compare, named at each path that holds it");
        assertEquals(Set.of(), gaps(walked), "nothing stopped this walk");
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

        Covered<Divergence> walked = Divergence.between(left, right);

        assertEquals(Set.of(" java.util.IdentityHashMap THE_SAME_THING_TWICE"), found(walked),
                "a map comparing by address, said as what it is");
        assertEquals(Set.of(), gaps(walked), "nothing stopped this walk");
    }

    /**
     * And a container comparing by address is named even when something under it also is.
     *
     * <p>Two defects and not one. What a container's equality rests on is its own business, and a
     * value it happens to hold is somebody else's — so a rule that names the holder only where
     * nothing was found beneath it lets a container be wrapped around a defect already written down
     * and go unnamed. What says this one is its own is that its keys pair by what they say and it
     * says they do not, which is true whatever its values did.
     */
    @Test
    void aContainerComparingByAddressIsNamedBesideWhatItHolds() {
        Map<Object, Object> left = new IdentityHashMap<>();
        Map<Object, Object> right = new IdentityHashMap<>();
        left.put(new String("k"), new Address());
        right.put(new String("k"), new Address());

        Covered<Divergence> walked = Divergence.between(left, right);

        assertEquals(Set.of(" java.util.IdentityHashMap THE_SAME_THING_TWICE",
                        "{value} " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "the map for its keys, and what it holds for itself");
    }

    /**
     * Two containers of one contract and two classes are one value.
     *
     * <p>A concrete class is not what makes a value. A {@code HashMap} and a {@code LinkedHashMap}
     * holding one thing are equal by the contract both answer to, and a walk that told them apart by
     * their class would report a compile that reproduced as one that did not — which it would only
     * ever do beside a real defect, since that is what starts the walk.
     */
    @Test
    void twoContainersOfOneContractAreNotTwoAnswers() {
        Covered<Divergence> walked = Divergence.between(
                new Held(new HashMap<>(Map.of("k", "v")), new Address()),
                new Held(new java.util.LinkedHashMap<>(Map.of("k", "v")), new Address()));

        assertEquals(Set.of(".Held#beside " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "only what does not compare is named");
    }

    /** And the same of two lists, which answer to a contract of their own. */
    @Test
    void twoListsOfOneContractAreNotTwoAnswers() {
        Covered<Divergence> walked = Divergence.between(
                new Held(new java.util.ArrayList<>(List.of("a")), new Address()),
                new Held(new java.util.LinkedList<>(List.of("a")), new Address()));

        assertEquals(Set.of(".Held#beside " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "only what does not compare is named");
    }

    /** And a collection with no rule for pairing is one whatever the two sizes are. */
    @Test
    void aCollectionWithNoRuleIsOneWhateverItsSize() {
        Address beside = new Address();
        Covered<Divergence> walked = Divergence.between(
                new Held(new java.util.ArrayDeque<>(List.of("a")), beside),
                new Held(new java.util.ArrayDeque<>(List.of("a", "b")), beside));

        assertEquals(Set.of("A_CONTAINER_WITH_NO_RULE_FOR_PAIRING .Held#it"), gaps(walked),
                "that two of different sizes hold different things is a contract too");
        assertEquals(Set.of(), found(walked), "and nothing is concluded from the sizes");
    }

    /** And a member step is told from a member step by what declares it, not by what it is shown
     *  as. */
    @Test
    void twoTypesOfOneShortNameAreTwoPlaces() {
        assertEquals(2, Set.of(
                        new Locus.Step.Member("a.Left$Case", "held"),
                        new Locus.Step.Member("b.Right$Case", "held")).size(),
                "two types called Case are two types");
        assertEquals(".Case#held",
                Locus.ROOT.then(new Locus.Step.Member("a.Left$Case", "held")).toString(),
                "and a reader is shown the short one");
    }

    /** And a map that holds different things still says so, which is what the above must not take
     *  away. */
    @Test
    void andAMapHoldingSomethingElseStillSaysSo() {
        Covered<Divergence> walked = Divergence.between(
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
        Covered<Divergence> walked = Divergence.between(
                java.util.Optional.of(new Address()), java.util.Optional.of(new Address()));

        assertEquals(Set.of("? " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "what is inside, named inside");
        assertEquals(Set.of(), gaps(walked), "and nothing stopped the walk");
    }

    /** And an absence against a thing is two different answers, which is not about equality. */
    @Test
    void andAnAbsenceAgainstAThingIsADifferentAnswer() {
        Covered<Divergence> walked = Divergence.between(
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

        Covered<Divergence> walked = Divergence.between(
                new Held(left, new Address()), new Held(right, new Address()));

        assertEquals(Set.of(".Held#beside " + Address.class.getName() + " THE_SAME_THING_TWICE"),
                found(walked), "the sets hold the same things, and only what is beside them differs");
        assertEquals(Set.of(), gaps(walked), "and nothing stopped the walk");
    }

    /**
     * Something to hold a container in, beside something that never compares.
     *
     * <p>Both halves. Held on its own, two of these are equal wherever the containers are, and the
     * walk stops at them without ever reaching what is inside — so the container's own rule would go
     * untested and the assertion would pass on a walk that never happened.
     */
    private record Held(Object it, Address beside) {}

    /** And a list is still paired by position, which is what a list's equality is. */
    @Test
    void aListIsPairedByPosition() {
        Address beside = new Address();
        Covered<Divergence> walked = Divergence.between(
                new Held(List.of("a", "b"), beside), new Held(List.of("b", "a"), beside));

        assertEquals(Set.of(".Held#it[] java.lang.String DIFFERENT_THINGS"), found(walked),
                "two lists holding the same things in two orders are two lists");
    }

    /** A collection that is neither is where the walk stops rather than guesses. */
    @Test
    void aCollectionThatIsNeitherAListNorASetStopsTheWalk() {
        Address beside = new Address();
        Covered<Divergence> walked = Divergence.between(
                new Held(new java.util.ArrayDeque<>(List.of("a")), beside),
                new Held(new java.util.ArrayDeque<>(List.of("a")), beside));

        assertEquals(Set.of("A_CONTAINER_WITH_NO_RULE_FOR_PAIRING .Held#it"), gaps(walked), "neither position nor membership is its equality");
        assertEquals(Set.of(), Set.of(),
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
        Covered<Divergence> walked = Divergence.between(
                new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)),
                new Dated(java.time.LocalDateTime.of(2026, 1, 2, 0, 0)));

        assertEquals(Set.of("A_FIELD_THAT_WOULD_NOT_OPEN .Dated#at.LocalDateTime#date",
                        "A_FIELD_THAT_WOULD_NOT_OPEN .Dated#at.LocalDateTime#time"),
                gaps(walked), "for the reason it is, and where");
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
        Covered<Divergence> walked = Divergence.between(
                new Root(new Holder(new Point(new Address())), new Holder(new Point(new Address()))),
                new Root(new Holder(new Point(new Address())), new Holder(new Point(new Address()))),
                1);

        assertEquals(Set.of("BUDGET_EXHAUSTED .Root#one", "BUDGET_EXHAUSTED .Root#two"),
                gaps(walked), "one pair is not the whole of that graph");
    }

    /** Two maps of one size whose keys line up with nothing. */
    @Test
    void twoMapsWhoseKeysDoNotPairAreWhereTheWalkStops() {
        Map<Object, Object> left = new HashMap<>();
        Map<Object, Object> right = new HashMap<>();
        left.put(new Address(), "v");
        right.put(new Address(), "v");

        Covered<Divergence> walked = Divergence.between(left, right);

        assertEquals(Set.of("MEMBERS_THAT_DO_NOT_PAIR {key}"), gaps(walked), "the entries line up with nothing");
        assertEquals(Set.of(), Set.of(),
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

        Covered<Divergence> walked = Divergence.between(left, right);

        assertEquals(Set.of("A_GRAPH_THAT_LOOPS .Loop#again"), gaps(walked), "the walk met the pair it was already walking");
        assertEquals(Set.of(), Set.of(),
                "for the reason it is, and where");
        assertEquals(Set.of(), found(walked),
                "and nothing is named for what the walk did not get to");
    }
}
