package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the walk of one answer says, asked of the walk itself rather than through a compile.
 *
 * <p>The register in {@link EverythingAnAnswerHoldsMeansSomethingTest} is worth what the two walks
 * under it are worth, and what a walk gets wrong does not show there. A walk that steps into a
 * container without asking the container anything comes back from a store looking exactly like one
 * that asked; a walk that remembers "already seen" rather than what it found reports one place for a
 * thing held in two; a walk that meets a field it cannot open and says nothing agrees with the
 * register about less than the register names.
 *
 * <p>So the shapes are built here. Each is the smallest object graph with the property, and each
 * assertion is about what the walk answers.
 *
 * <p>{@link APairWalkNamesADefectWhereItIsTest} is the same for the other detector. The two are
 * apart because the walks are: this one holds one thing and asks each object what it is, that one
 * holds two and asks where they come apart.
 */
class AWalkOfOneAnswerNamesWhatMeansNothingTest {

    /** Something that says which object it is and nothing else. */
    private static final class Address {}

    /** And two ways down to one of those. */
    private record Holder(Address held) {}

    private record Root(Holder one, Holder two) {}

    private static List<AnswerWalk.Found> foundBy(AnswerWalk.Walked walked) {
        return switch (walked.covered()) {
            case Covered.Whole<AnswerWalk.Found>(List<AnswerWalk.Found> all) -> all;
            case Covered.Partly<AnswerWalk.Found>(List<AnswerWalk.Found> all, List<Gap> _) -> all;
        };
    }

    private static Set<String> places(AnswerWalk.Walked walked) {
        Set<String> out = new TreeSet<>();
        foundBy(walked).forEach(each -> out.add(each.place().asText()));
        return out;
    }

    /** And where the walk fell short, which is empty exactly where it did not. */
    private static Set<String> gaps(AnswerWalk.Walked walked) {
        Set<String> out = new TreeSet<>();
        if (walked.covered() instanceof Covered.Partly<AnswerWalk.Found>(
                List<AnswerWalk.Found> _, List<Gap> gaps)) {
            gaps.forEach(each -> out.add(each.toString()));
        }
        return out;
    }

    /**
     * A thing two paths reach is named at both.
     *
     * <p>What is remembered per object has to be what was found under it rather than the fact of
     * having been there. Remembered as "already seen", the second path comes back with nothing and a
     * register of places holds whichever path the walk happened to take first — so which place is
     * written down would move with the order of a walk.
     */
    @Test
    void aThingTwoPathsHoldIsNamedAtBoth() {
        Holder shared = new Holder(new Address());

        AnswerWalk.Walked walked = AnswerWalk.of("Q", new Root(shared, shared));

        assertEquals(Set.of("Q.Root#one.Holder#held " + Address.class.getName(),
                        "Q.Root#two.Holder#held " + Address.class.getName()),
                places(walked), "the thing that means nothing, named at each place that holds it");
        assertEquals(Set.of(), gaps(walked), "nothing stopped this walk");
    }

    /**
     * A container is asked what it is before it is stepped into.
     *
     * <p>An array's equality is its address whatever it holds, so an answer holding one can never
     * equal its own recomputation however ordinary everything inside it is. Walked into without being
     * asked, it is the one container the language gives no equality to at all and the one this would
     * never name.
     */
    @Test
    void anArrayIsNamedRatherThanSteppedInto() {
        AnswerWalk.Walked walked = AnswerWalk.of("Q", List.of(new byte[] {1, 2}));

        assertEquals(Set.of("Q[] byte[]"), places(walked),
                "the array itself, and not what is in it");
    }

    /** A key whose equality is over part of itself, so it carries more than it compares. */
    private static final class Named {
        private final String name;
        private final Address held;

        private Named(String name, Address held) {
            this.name = name;
            this.held = held;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Named named && named.name.equals(name);
        }

        @Override
        public int hashCode() {
            return name.hashCode();
        }
    }

    /**
     * A key is walked as well as a value.
     *
     * <p>A key is as much of an answer as a value is. This is the walk that can find something in
     * one: the walk that holds two answers together pairs keys by what they say, so a key it pairs
     * is a key equal to the other side and there is nothing under it left to find.
     */
    @Test
    void aKeyIsWalkedAsWellAsAValue() {
        Map<Object, Object> held = new HashMap<>();
        held.put(new Named("k", new Address()), "v");

        assertEquals(Set.of("Q{key}.Named#held " + Address.class.getName()),
                places(AnswerWalk.of("Q", held)), "what a key carries, reached through the key");
    }

    /** And what an absence holds is walked, which the field under it would never let happen. */
    @Test
    void whatAnAbsenceHoldsIsWalked() {
        assertEquals(Set.of("Q? " + Address.class.getName()),
                places(AnswerWalk.of("Q", Optional.of(new Address()))),
                "what is inside, named inside");
    }

    /**
     * A graph that holds itself is said out loud rather than passed over.
     *
     * <p>Through a thing that says what it is, because that is the only way a walk gets round twice:
     * something with no equality of its own is named where it stands and never stepped into, so a
     * ring made of those has nothing to go round.
     */
    @Test
    void aGraphThatHoldsItselfIsSaidOutLoud() {
        List<Object> ring = new java.util.ArrayList<>();
        ring.add(ring);

        AnswerWalk.Walked walked = AnswerWalk.of("Q", ring);

        assertEquals(Set.of("A_GRAPH_THAT_LOOPS Q[] java.util.ArrayList"), gaps(walked),
                "for what it is, and where");
    }

    /** Something whose insides belong to a module that opens nothing here. */
    private record Dated(java.time.LocalDateTime at) {}

    /**
     * A field the runtime will not hand over is said out loud.
     *
     * <p>What is under it was never asked about. Swallowed, a walk that could not get into half the
     * answers would agree with the register as readily as one that read all of them.
     */
    @Test
    void aFieldThatWouldNotOpenIsSaidOutLoud() {
        AnswerWalk.Walked walked = AnswerWalk.of("Q",
                new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0)));

        assertEquals(Set.of("A_FIELD_THAT_WOULD_NOT_OPEN Q.Dated#at.LocalDateTime#date",
                        "A_FIELD_THAT_WOULD_NOT_OPEN Q.Dated#at.LocalDateTime#time"),
                gaps(walked), "and says which fields");
    }

    /**
     * What the language ships that says it keeps none of the contract is held to saying so.
     *
     * <p>The rule that reads a thing for what it holds rests on comparing it comparing them, and
     * the language ships one that says it does the opposite. Named and not noticed, this walk would
     * read one for its entries and never ask the map itself — so what is named is held to failing
     * the very thing the rule claims, and a name here that turned out to keep it would be something
     * excluded for nothing.
     */
    @Test
    void whatIsNamedAsKeepingNoneOfTheContractKeepsNoneOfIt() {
        Set<String> keptItAfterAll = new TreeSet<>();
        for (Class<?> each : AnswerShape.whichKeepNoneOfIt()) {
            if (twoOfThemSayingTheSameThingAreEqual(each)) {
                keptItAfterAll.add(each.getName());
            }
        }

        assertEquals(Set.of(), keptItAfterAll,
                "named as keeping none of the contract, and keeping it");
    }

    /**
     * And what is read for what it holds keeps it.
     *
     * <p>The other half, over what a store actually holds rather than over a list somebody wrote:
     * every container met while walking one is asked whether two of it saying the same thing are
     * the same thing. One that is not would be read for its members and never asked, which is the
     * shape the name above exists for.
     */
    @Test
    void whatIsReadForWhatItHoldsKeepsTheContract() {
        Set<String> saidNo = new TreeSet<>();
        for (Supplier<Object> each : theWaysAnAnswerHoldsThings()) {
            Object one = each.get();
            if (AnswerShape.keepsThatContract(one.getClass()) && !one.equals(each.get())) {
                saidNo.add(one.getClass().getName());
            }
        }

        assertEquals(Set.of(), saidNo, "read for what it holds, and comparing two of them does not"
                + " compare what they hold");
    }

    /**
     * How an answer comes to hold a collection, a map or an absence, one way per line.
     *
     * <p>Built twice from one line rather than reflected into: what the language hands back for one
     * of these is its own business — a list of one thing and a list of many are two classes — and
     * what is asked is what an answer would hold, not what a name can be constructed.
     */
    private static List<Supplier<Object>> theWaysAnAnswerHoldsThings() {
        return List.of(
                () -> Map.of(new String("a"), new String("b")),
                () -> new LinkedHashMap<>(Map.of(new String("a"), new String("b"))),
                () -> new HashMap<>(Map.of(new String("a"), new String("b"))),
                () -> new java.util.TreeMap<>(Map.of(new String("a"), new String("b"))),
                () -> java.util.Collections.unmodifiableMap(
                        new LinkedHashMap<>(Map.of(new String("a"), new String("b")))),
                () -> List.of(new String("a")),
                () -> List.of(new String("a"), new String("b"), new String("c")),
                () -> new java.util.ArrayList<>(List.of(new String("a"))),
                () -> java.util.Collections.unmodifiableList(
                        new java.util.ArrayList<>(List.of(new String("a")))),
                () -> Set.of(new String("a")),
                () -> new java.util.LinkedHashSet<>(Set.of(new String("a"))),
                () -> new java.util.HashSet<>(Set.of(new String("a"))),
                () -> java.util.Collections.unmodifiableSet(
                        new java.util.LinkedHashSet<>(Set.of(new String("a")))),
                () -> Optional.of(new String("a")),
                // And the one that is named as keeping none of it, so that a line above going
                // quiet is not the whole of what this says.
                () -> {
                    Map<Object, Object> byWhichObject = new java.util.IdentityHashMap<>();
                    byWhichObject.put(new String("a"), new String("b"));
                    return byWhichObject;
                });
    }

    /**
     * Whether two of these built apart, holding what compares equal, compare equal.
     *
     * <p>Which is the whole of the contract: a walk that reads one for its members is saying that
     * comparing two of them is comparing the members. Asked by building two, because nothing a
     * class says about itself distinguishes one that keeps this from one that does not.
     */
    private static boolean twoOfThemSayingTheSameThingAreEqual(Class<?> type) {
        for (Supplier<Object> each : theWaysAnAnswerHoldsThings()) {
            if (each.get().getClass() == type) {
                return each.get().equals(each.get());
            }
        }
        throw new IllegalStateException("nothing here builds a " + type.getName()
                + ", so nothing here says whether it keeps the contract");
    }

    /** And two ways down to one of those. */
    private record BothWays(Dated one, Dated two) {}

    /**
     * A thing the walk got only part way into is not put away as looked at.
     *
     * <p>What is remembered per thing is what was found under it, and it may be remembered only
     * where that is the whole of what is there. Remembered after a walk that could not open half of
     * it, the next path to hold the same thing is told there was nothing to see — and the place
     * where the walk fell short is a place the register never hears about, while the walk that met
     * it says it covered everything.
     */
    @Test
    void aThingTheWalkGotPartWayIntoIsNotRememberedAsWalked() {
        Dated shared = new Dated(java.time.LocalDateTime.of(2026, 1, 1, 0, 0));

        AnswerWalk.Walked walked = AnswerWalk.of("Q", new BothWays(shared, shared));

        assertEquals(Set.of("A_FIELD_THAT_WOULD_NOT_OPEN Q.BothWays#one.Dated#at.LocalDateTime#date",
                        "A_FIELD_THAT_WOULD_NOT_OPEN Q.BothWays#one.Dated#at.LocalDateTime#time",
                        "A_FIELD_THAT_WOULD_NOT_OPEN Q.BothWays#two.Dated#at.LocalDateTime#date",
                        "A_FIELD_THAT_WOULD_NOT_OPEN Q.BothWays#two.Dated#at.LocalDateTime#time"),
                gaps(walked), "the walk fell short at both places that hold it");
    }
}
