package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

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

    private static List<String> warnings(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return compilation.warnings().stream().map(each -> each.diagnostic().code()).toList();
    }
}
