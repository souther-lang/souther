package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ClosedState;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition that a set does or does not hold a value is read by how many of its elements are the
 * value, and so is what an insert of the value into it answers.
 *
 * <p>Two laws of the library meet at that number: that a set holds a value is some element of it
 * being the value, and an insert holds one more than its set where none is and as many where one
 * is. And of the elements of another container, an insert holds those its set held and perhaps the
 * value, which is how many an intersection with it holds. So a guard that a value is not in a set
 * says how many the insert holds, and that it keeps the set apart from another set the value is
 * not in.
 */
class AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest {

    private static final String SEATS = """
            module seats

            data Seats = { taken: Set<Int>, free: Int, cap: Int }
                invariant Set.size(taken) + free == cap && free >= 0

            """;

    private static final String OUTCOMES = """
            module outcomes

            data Outcomes = { seated: Set<Int>, refused: Set<Int> }
                invariant Set.isEmpty(Set.intersection(seated, refused))

            """;

    @Test
    void aValueNotInTheSetMakesTheInsertOneLarger() {
        assertEquals(List.of(), warnings(SEATS + """
                behavior take : (s: Seats, n: Int) -> Seats | Already | Full
                    constructs Seats
                let take (s, n) = {
                    guard Bool.not(Set.contains(n, s.taken)) else Already
                    guard s.free > 0 else Full
                    Seats { ...s, taken = Set.insert(n, s.taken), free = s.free - 1 }
                }
                """));
    }

    /** Where a value is not in a set, the insert of it holds one more, as {@code taken + 1} does of
     *  a count. So what the invariants and the guards show of the seats kept as a set is what they
     *  show of the seats kept as a count, whichever way the invariants are declared and whether or
     *  not the guard on the free seats is there. */
    @Test
    void aSetOfSeatsIsReadAsTheCountOfThemIs() {
        for (boolean guardsFree : new boolean[] {true, false}) {
            for (boolean balanceFirst : new boolean[] {true, false}) {
                String balance = "invariant balance = %s + free == cap && free >= 0";
                String within = "invariant withinCap = %s <= cap";
                String freeGuard = guardsFree ? "guard s.free > 0 else Full" : "";
                List<String> asSet = warnings("""
                        module seats

                        data Seats = { taken: Set<Int>, free: Int, cap: Int }
                            %s
                            %s

                        behavior take : (s: Seats, n: Int) -> Seats | Already | Full
                            constructs Seats
                        let take (s, n) = {
                            guard Bool.not(Set.contains(n, s.taken)) else Already
                            %s
                            Seats { ...s, taken = Set.insert(n, s.taken), free = s.free - 1 }
                        }
                        """.formatted(
                        (balanceFirst ? balance : within).formatted("Set.size(taken)"),
                        (balanceFirst ? within : balance).formatted("Set.size(taken)"),
                        freeGuard));
                List<String> asCount = warnings("""
                        module seats

                        data Seats = { taken: Int, free: Int, cap: Int }
                            %s
                            %s

                        behavior take : (s: Seats, n: Int) -> Seats | Full
                            constructs Seats
                        let take (s, n) = {
                            %s
                            Seats { ...s, taken = s.taken + 1, free = s.free - 1 }
                        }
                        """.formatted(
                        (balanceFirst ? balance : within).formatted("taken"),
                        (balanceFirst ? within : balance).formatted("taken"),
                        freeGuard));
                assertEquals(asCount, asSet, "guardsFree=" + guardsFree + " balanceFirst=" + balanceFirst);
                assertEquals(guardsFree, asSet.isEmpty(), "the guard on the free seats is not spare");
            }
        }
    }

    @Test
    void theConditionReadEitherWayIsTheSameNumber() {
        assertEquals(List.of(), warnings(SEATS + """
                behavior take : (s: Seats, n: Int) -> Seats | Already | Full
                    constructs Seats
                let take (s, n) =
                    if Set.contains(n, s.taken) then Already
                    else if s.free > 0 then Seats { ...s, taken = Set.insert(n, s.taken), free = s.free - 1 }
                    else Full
                """));
    }

    @Test
    void aValueInTheSetLeavesTheInsertAsLarge() {
        assertEquals(List.of(), warnings(SEATS + """
                behavior keep : (s: Seats, n: Int) -> Seats | Fresh
                    constructs Seats
                let keep (s, n) = {
                    guard Set.contains(n, s.taken) else Fresh
                    Seats { ...s, taken = Set.insert(n, s.taken) }
                }
                """));
    }

    @Test
    void anInsertWithNothingSaidOfTheValueMayBeEitherSize() {
        assertEquals(List.of("E2011"), warnings(SEATS + """
                behavior take : (s: Seats, n: Int) -> Seats | Full
                    constructs Seats
                let take (s, n) = {
                    guard s.free > 0 else Full
                    Seats { ...s, taken = Set.insert(n, s.taken), free = s.free - 1 }
                }
                """));
    }

    @Test
    void aValueNotInTheOtherSetKeepsTheTwoApart() {
        assertEquals(List.of(), warnings(OUTCOMES + """
                behavior refuse : (o: Outcomes, n: Int) -> Outcomes | Already
                    constructs Outcomes
                let refuse (o, n) = {
                    guard Bool.not(Set.contains(n, o.seated)) else Already
                    Outcomes { ...o, refused = Set.insert(n, o.refused) }
                }
                """));
    }

    /** The set counted from grows as well: of its elements, the other set holds those it held and
     *  perhaps the value. */
    @Test
    void anInsertIntoTheSetCountedFromKeepsTheTwoApartToo() {
        assertEquals(List.of(), warnings("""
                module outcomes

                data Outcomes = { seated: Set<Int>, refused: Set<Int> }
                    invariant Set.isEmpty(Set.intersection(refused, seated))

                behavior refuse : (o: Outcomes, n: Int) -> Outcomes | Already
                    constructs Outcomes
                let refuse (o, n) = {
                    guard Bool.not(Set.contains(n, o.seated)) else Already
                    Outcomes { ...o, refused = Set.insert(n, o.refused) }
                }
                """));
    }

    @Test
    void aValueSaidNotInAnotherSetSaysNothingOfTheTwo() {
        assertEquals(List.of("E2011"), warnings(OUTCOMES + """
                behavior refuse : (o: Outcomes, n: Int) -> Outcomes | Already
                    constructs Outcomes
                let refuse (o, n) = {
                    guard Bool.not(Set.contains(n, o.refused)) else Already
                    Outcomes { ...o, refused = Set.insert(n, o.refused) }
                }
                """));
    }

    @Test
    void anotherValueSaidNotInTheSetSaysNothingOfTheOneInserted() {
        assertEquals(List.of("E2011"), warnings(OUTCOMES + """
                behavior refuse : (o: Outcomes, n: Int, m: Int) -> Outcomes | Already
                    constructs Outcomes
                let refuse (o, n, m) = {
                    guard Bool.not(Set.contains(m, o.seated)) else Already
                    Outcomes { ...o, refused = Set.insert(n, o.refused) }
                }
                """));
    }

    private static final String LEDGER = """
            module ledger

            data Ledger = { amounts: Map<String, Int>, count: Int }
                invariant Map.size(amounts) == count

            """;

    /** A map holds a key once, so a key it does not hold yet is one entry more, and one it holds
     *  is as many. */
    @Test
    void aKeyNotInTheMapMakesTheInsertOneLarger() {
        assertEquals(List.of(), warnings(LEDGER + """
                behavior open : (l: Ledger, k: String) -> Ledger | AlreadyOpen
                    constructs Ledger
                let open (l, k) = {
                    guard Bool.not(Map.containsKey(k, l.amounts)) else AlreadyOpen
                    Ledger { amounts = Map.insert(k, 0, l.amounts), count = l.count + 1 }
                }

                behavior amend : (l: Ledger, k: String, v: Int) -> Ledger | Missing
                    constructs Ledger
                let amend (l, k, v) = {
                    guard Map.containsKey(k, l.amounts) else Missing
                    Ledger { ...l, amounts = Map.insert(k, v, l.amounts) }
                }
                """));
    }

    @Test
    void anInsertWithNothingSaidOfTheKeyMayBeEitherSize() {
        assertEquals(List.of("E2011"), warnings(LEDGER + """
                behavior open : (l: Ledger, k: String) -> Ledger
                    constructs Ledger
                let open (l, k) = Ledger { amounts = Map.insert(k, 0, l.amounts), count = l.count + 1 }
                """));
    }

    /** A removal is read by the same count: one fewer where the value or key was there. */
    @Test
    void aValueInTheSetMakesTheRemovalOneSmaller() {
        assertEquals(List.of(), warnings(SEATS + """
                behavior release : (s: Seats, n: Int) -> Seats | NotTaken
                    constructs Seats
                let release (s, n) = {
                    guard Set.contains(n, s.taken) else NotTaken
                    Seats { ...s, taken = Set.remove(n, s.taken), free = s.free + 1 }
                }
                """ + LEDGER.replace("module ledger\n", "") + """
                behavior close : (l: Ledger, k: String) -> Ledger | Closed
                    constructs Ledger
                let close (l, k) = {
                    guard Map.containsKey(k, l.amounts) else Closed
                    Ledger { amounts = Map.remove(k, l.amounts), count = l.count - 1 }
                }
                """));
    }

    /** What a union adds is the other set's elements, so a set apart from both halves is apart
     *  from the union. */
    @Test
    void aUnionOfSetsApartFromAnotherIsApartFromItToo() {
        assertEquals(List.of(), warnings(OUTCOMES + """
                behavior refuseAll : (o: Outcomes, ns: Set<Int>) -> Outcomes | Already
                    constructs Outcomes
                let refuseAll (o, ns) = {
                    guard Set.isEmpty(Set.intersection(o.seated, ns)) else Already
                    Outcomes { ...o, refused = Set.union(o.refused, ns) }
                }
                """));
    }

    /** Both sides built: the union is taken apart first, so the value inserted on the other side is
     *  asked of each half as a condition says it. */
    @Test
    void aUnionOnOneSideAndAnInsertOnTheOtherAreTakenApartTogether() {
        assertEquals(List.of(), warnings(OUTCOMES + """
                behavior move : (o: Outcomes, ns: Set<Int>, n: Int) -> Outcomes | Already
                    constructs Outcomes
                let move (o, ns, n) = {
                    guard Set.isEmpty(Set.intersection(ns, o.refused)) else Already
                    guard Bool.not(Set.contains(n, o.seated)) else Already
                    guard Bool.not(Set.contains(n, ns)) else Already
                    Outcomes { seated = Set.union(o.seated, ns), refused = Set.insert(n, o.refused) }
                }
                """));
    }

    /** {@code depth} values added on each side of the two sets. */
    static String insertsOnBothSides(int depth) {
        StringBuilder parameters = new StringBuilder();
        StringBuilder names = new StringBuilder();
        String seated = "o.seated";
        String refused = "o.refused";
        for (int i = 0; i < depth; i++) {
            parameters.append(", a").append(i).append(": Int, b").append(i).append(": Int");
            names.append(", a").append(i).append(", b").append(i);
            seated = "Set.insert(a" + i + ", " + seated + ")";
            refused = "Set.insert(b" + i + ", " + refused + ")";
        }
        return OUTCOMES + """
                behavior both : (o: Outcomes%s) -> Outcomes
                    constructs Outcomes
                let both (o%s) = Outcomes { seated = %s, refused = %s }
                """.formatted(parameters, names, seated, refused);
    }

    /** {@code depth} values inserted one into another, under a cap {@code depth} higher. */
    static String aChainOfInserts(int depth) {
        StringBuilder parameters = new StringBuilder();
        StringBuilder names = new StringBuilder();
        String taken = "s.taken";
        for (int i = 0; i < depth; i++) {
            parameters.append(", a").append(i).append(": Int");
            names.append(", a").append(i);
            taken = "Set.insert(a" + i + ", " + taken + ")";
        }
        return """
                module seats

                data Capped = { taken: Set<Int>, cap: Int }
                    invariant Set.size(taken) <= cap

                behavior grow : (s: Capped%s) -> Capped
                    constructs Capped
                let grow (s%s) = Capped { taken = %s, cap = s.cap + %d }
                """.formatted(parameters, names, taken, depth);
    }

    /** A set united with itself {@code depth} times over. */
    static String aSetUnitedWithItself(int depth) {
        StringBuilder lets = new StringBuilder();
        for (int i = 1; i <= depth; i++) {
            lets.append("    let s").append(i).append(" = Set.union(s").append(i - 1)
                    .append(", s").append(i - 1).append(")\n");
        }
        return OUTCOMES + """
                behavior refuseAll : (o: Outcomes) -> Outcomes
                    constructs Outcomes
                let refuseAll (o) = {
                    let s0 = o.refused
                %s    Outcomes { ...o, refused = s%d }
                }
                """.formatted(lets, depth);
    }

    /** How many times a premise was looked at for a question while {@code source} was read. */
    private static long premisesWorkedReading(String source) {
        long before = ClosedState.premisesWorked();
        warnings(source);
        return ClosedState.premisesWorked() - before;
    }

    /**
     * What a program costs grows with how many it says of a kind and not with how many pairs of
     * them there are.
     *
     * <p>A closure is made for each place a path has got to, holds the rules said so far, and asks
     * every premise for each position of each of them, so the premises looked at between them grow
     * as the cube of the depth: twice the depth is eight times as many. Reading the pairs of what is
     * said as well takes them to the fourth power, which is sixteen times as many, and the bound
     * sits between the two. Counted rather than timed: that is a shape, and how long it takes is
     * the machine's.
     */
    private static void assertGrowsNoFasterThanTheCube(IntFunction<String> program) {
        long shallow = premisesWorkedReading(program.apply(4));
        long twiceAsDeep = premisesWorkedReading(program.apply(8));
        assertTrue(twiceAsDeep < 12 * shallow, "twice the depth looked at " + twiceAsDeep
                + " premises where the shallower looked at " + shallow
                + ", which is more than the cube of the depth allows");
    }

    /** Values added on both sides are read one side at a time, so the counts named grow with how
     *  many were added and not with how many pairs of them there are. */
    @Test
    void manyInsertsOnBothSidesAreReadOneSideAtATime() {
        assertEquals(List.of("E2011"), warnings(insertsOnBothSides(4)));
        assertGrowsNoFasterThanTheCube(AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest
                ::insertsOnBothSides);
    }

    /** How many a set holds once a value is put in is one form of the count of that value, and
     *  no case of it: inserts written one into another are each read once, and together are as
     *  many more as there were inserts at most. */
    @Test
    void aChainOfInsertsHoldsAtMostOneMoreForEach() {
        assertEquals(List.of(), warnings(aChainOfInserts(4)));
        assertGrowsNoFasterThanTheCube(
                AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest::aChainOfInserts);
    }

    /** What a count of two containers carries is filed once for the values it is read off, so a
     *  set united with itself again and again is read once for each union and not once for each
     *  way down to it. */
    @Test
    void aSetUnitedWithItselfIsReadOnceForEachUnion() {
        assertEquals(List.of(), warnings(aSetUnitedWithItself(4)));
        assertGrowsNoFasterThanTheCube(
                AGuardThatAValueIsNotInASetIsReadByWhatAnInsertOfItAnswersTest
                        ::aSetUnitedWithItself);
    }

    @Test
    void aUnionWithASetNothingIsSaidOfMayMeetTheOther() {
        assertEquals(List.of("E2011"), warnings(OUTCOMES + """
                behavior refuseAll : (o: Outcomes, ns: Set<Int>) -> Outcomes
                    constructs Outcomes
                let refuseAll (o, ns) = Outcomes { ...o, refused = Set.union(o.refused, ns) }
                """));
    }

    /** The keys of two maps are kept apart the way two sets are. */
    @Test
    void aKeyNotInTheOtherMapKeepsTheirKeysApart() {
        assertEquals(List.of(), warnings("""
                module books

                data Books = { open: Map<String, Int>, closed: Map<String, Int> }
                    invariant Map.isEmpty(Map.intersection(open, closed))

                behavior close : (b: Books, k: String) -> Books | StillOpen
                    constructs Books
                let close (b, k) = {
                    guard Bool.not(Map.containsKey(k, b.open)) else StillOpen
                    Books { ...b, closed = Map.insert(k, 0, b.closed) }
                }
                """));
    }

    @Test
    void theBoundsAnInsertWasAlreadyReadByStillHold() {
        assertEquals(List.of(), warnings("""
                module bounds

                data NonEmpty = { ids: Set<Int> }
                    invariant Set.size(ids) >= 1

                behavior grow : (s: Set<Int>, n: Int) -> NonEmpty
                    constructs NonEmpty
                let grow (s, n) = NonEmpty { ids = Set.insert(n, s) }

                data Capped = { taken: Set<Int>, cap: Int }
                    invariant Set.size(taken) <= cap

                behavior admit : (e: Capped, n: Int) -> Capped | Full
                    constructs Capped
                let admit (e, n) = {
                    guard Set.size(e.taken) < e.cap else Full
                    Capped { ...e, taken = Set.insert(n, e.taken) }
                }
                """));
    }

    static List<String> warnings(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        ACompiledModel.compiles(compilation);
        return compilation.warnings().stream().map(each -> each.diagnostic().code()).toList();
    }
}
