package souther.compiler;

import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a library operation guarantees of its answer, or of what it hands its closure, is known at a
 * construction built from it.
 *
 * <p>Every row builds a newtype whose invariant is exactly what the operation guarantees, so the
 * construction is discharged by the operation and by nothing else the model writes. The controls
 * leave out the one thing a guarantee stands on and are still reported.
 */
class WhatALibraryOperationGuaranteesReachesAnInvariantTest {

    /** The behavior {@code f} with {@code signature}, constructing {@code built}, defined by
     * {@code body}. */
    private static List<String> reported(String signature, String built, String body) {
        return reported("", signature, built, body);
    }

    /** The same, beside {@code declarations} of its own. */
    private static List<String> reported(String declarations, String signature, String built,
                                         String body) {
        String source = """
                module demo

                data Idx = Int
                    invariant value >= 0

                data NonPos = Int
                    invariant value <= 0

                data Pos = Int
                    invariant value > 0

                data Small = Int
                    invariant value >= 1 && value <= 10

                %s
                behavior f : %s
                    constructs %s

                let f %s
                """.formatted(declarations, signature, built, body);
        return Compiler.compileWithWarnings(source).warnings().stream()
                .map(Diagnostic::code)
                .distinct()
                .toList();
    }

    private static List<String> remainder(String built, String body) {
        return reported("(a: Int, n: Int) -> " + built, built, "(a, n) = " + body);
    }

    private static List<String> overList(String answer, String built, String body) {
        return reported("(xs: List<Int>) -> " + answer, built, "(xs) = " + body);
    }

    @Test
    void aRemainderByADivisorAboveNoughtTheGuardStatesIsNotNegative() {
        assertEquals(List.of(),
                remainder("Idx", "if n > 0 then Idx(Int.floorMod(a, n)) else Idx(0)"));
    }

    @Test
    void aDivisorAtOrAboveOneIsAboveNought() {
        assertEquals(List.of(),
                remainder("Idx", "if n >= 1 then Idx(Int.floorMod(a, n)) else Idx(0)"));
    }

    @Test
    void aDivisorThePathPinsToAPositiveNumberIsAboveNought() {
        assertEquals(List.of(),
                remainder("Idx", "if n == 7 then Idx(Int.floorMod(a, n)) else Idx(0)"));
    }

    @Test
    void aDivisorWhoseTypeIsPositiveIsAboveNought() {
        assertEquals(List.of(), reported("(a: Int, n: Pos) -> Idx", "Idx",
                "(a, n) = Idx(Int.floorMod(a, n.value))"));
    }

    @Test
    void theRemainderNamedBeforeTheGuardIsStillReadUnderIt() {
        assertEquals(List.of(), remainder("Idx", """
                {
                    let r = Int.floorMod(a, n)
                    if n > 0 then Idx(r) else Idx(0)
                }"""));
    }

    @Test
    void aRemainderByADivisorBelowNoughtIsNotPositive() {
        assertEquals(List.of(),
                remainder("NonPos", "if n < 0 then NonPos(Int.floorMod(a, n)) else NonPos(0)"));
    }

    @Test
    void theRemainderIsBelowTheDivisor() {
        assertEquals(List.of(), remainder("Small",
                "if n > 0 && n <= 10 then Small(Int.floorMod(a, n) + 1) else Small(1)"));
    }

    /** The divisor is a value the library derives: a clamp from one to ten is above nought on every
     * path, and the guarantee waits on what is derived of it. */
    @Test
    void aDivisorThatIsAClampAboveNoughtIsAboveNought() {
        assertEquals(List.of(),
                remainder("Idx", "Idx(Int.floorMod(a, Int.clamp(1, 10, n)))"));
    }

    @Test
    void aDivisorThatIsAClampGivenANameIsAboveNought() {
        assertEquals(List.of(), remainder("Idx", """
                {
                    let d = Int.clamp(1, 10, n)
                    Idx(Int.floorMod(a, d))
                }"""));
    }

    /** The control: a clamp that can end below nought leaves the divisor on neither side. */
    @Test
    void aDivisorThatIsAClampFromBelowNoughtIsOnNeitherSide() {
        assertEquals(List.of("E2011"),
                remainder("Idx", "Idx(Int.floorMod(a, Int.clamp(-5, 10, n)))"));
    }

    /** A remainder is itself a guarantee the next one waits on: the remainder by a divisor above
     * nought is not negative, and one more than it is above nought. */
    @Test
    void aDivisorThatIsAGuaranteedRemainderPlusOneIsAboveNought() {
        assertEquals(List.of(), reported("(a: Int, b: Int, n: Int) -> Idx", "Idx", """
                (a, b, n) = if n > 0
                    then Idx(Int.floorMod(a, Int.floorMod(b, n) + 1))
                    else Idx(0)"""));
    }

    /** The control: without the guard the inner remainder is of no known sign. */
    @Test
    void aDivisorThatIsAnUnguardedRemainderPlusOneIsOnNeitherSide() {
        assertEquals(List.of("E2011"), reported("(a: Int, b: Int, n: Int) -> Idx", "Idx", """
                (a, b, n) = Idx(Int.floorMod(a, Int.floorMod(b, n) + 1))"""));
    }

    @Test
    void aDivisorThatIsAProductOfTwoValuesAboveNoughtIsAboveNought() {
        assertEquals(List.of(), reported("(a: Int, x: Int, y: Int) -> Idx", "Idx", """
                (a, x, y) = if x > 0 && y > 0
                    then Idx(Int.floorMod(a, x * y))
                    else Idx(0)"""));
    }

    /** The control: nothing puts the divisor on either side of nought. */
    @Test
    void aDivisorOfNoKnownSignLeavesTheRemainderUnread() {
        assertEquals(List.of("E2011"), remainder("Idx", "Idx(Int.floorMod(a, n))"));
    }

    /** The control: the guard is on the other side of nought, where the remainder is not above it. */
    @Test
    void aDivisorBelowNoughtDoesNotMakeTheRemainderNotNegative() {
        assertEquals(List.of("E2011"),
                remainder("Idx", "if n < 0 then Idx(Int.floorMod(a, n)) else Idx(0)"));
    }

    @Test
    void theIndexMapIndexedHandsItsClosureIsNotNegative() {
        assertEquals(List.of(), overList("List<Idx>", "Idx",
                "List.mapIndexed((i, x) -> Idx(i), xs)"));
    }

    /** The index is below how many the list holds, which a record keeping the two apart states. */
    @Test
    void theIndexMapIndexedHandsItsClosureIsBelowHowManyTheListHolds() {
        assertEquals(List.of(), reported("""
                data Place = { at: Int, of: Int }
                    invariant at >= 0 && at < of
                """, "(xs: List<Int>) -> List<Place>", "Place",
                "(xs) = List.mapIndexed((i, x) -> Place { at = i, of = List.length(xs) }, xs)"));
    }

    /** The control: one past the index is not below how many the list holds. */
    @Test
    void theIndexPlusOneIsNotKnownBelowHowManyTheListHolds() {
        assertEquals(List.of("E2011"), reported("""
                data Place = { at: Int, of: Int }
                    invariant at >= 0 && at < of
                """, "(xs: List<Int>) -> List<Place>", "Place",
                "(xs) = List.mapIndexed((i, x) -> Place { at = i + 1, of = List.length(xs) }, xs)"));
    }

    /** The control: one less than the index is not known to be above nought. */
    @Test
    void theIndexLessOneIsNotKnownNotNegative() {
        assertEquals(List.of("E2011"), overList("List<Idx>", "Idx",
                "List.mapIndexed((i, x) -> Idx(i - 1), xs)"));
    }

    @Test
    void anElementOfARangeIsBetweenItsEnds() {
        assertEquals(List.of(), reported("(n: Int) -> List<Pos>", "Pos",
                "(n) = if n >= 1 then List.map(k -> Pos(k), List.rangeInclusive(1, n)) else []"));
    }

    @Test
    void anElementTheFindFoundMeetsThePredicate() {
        assertEquals(List.of(), overList("Pos", "Pos", """
                match List.find(k -> k > 3, xs) with
                    | Some k -> Pos(k)
                    | None -> Pos(1)"""));
    }

    @Test
    void anElementTheFilterKeptMeetsThePredicate() {
        assertEquals(List.of(), overList("List<Idx>", "Idx",
                "List.map(x -> Idx(x), List.filter(x -> x >= 0, xs))"));
    }

    @Test
    void anElementTheFilterKeptIsReadThroughTheNameItWasGiven() {
        assertEquals(List.of(), overList("List<Idx>", "Idx", """
                {
                    let kept = List.filter(x -> x >= 0, xs)
                    List.map(x -> Idx(x), kept)
                }"""));
    }

    @Test
    void anElementTheFilterKeptSurvivesAConstructionThatKeepsElements() {
        assertEquals(List.of(), overList("List<Idx>", "Idx",
                "List.map(x -> Idx(x), List.reverse(List.take(3, List.filter(x -> x >= 0, xs))))"));
    }

    @Test
    void theValueFindFoundIsReadThroughTheNameItWasGiven() {
        assertEquals(List.of(), overList("Pos", "Pos", """
                {
                    let found = List.find(k -> k > 3, xs)
                    match found with
                        | Some k -> Pos(k)
                        | None -> Pos(1)
                }"""));
    }

    /** The control: the predicate the closure answers is the one the value meets and no other. */
    @Test
    void theValueFindFoundMeetsOnlyThePredicateItWasFoundBy() {
        assertEquals(List.of("E2011"), overList("Pos", "Pos", """
                match List.find(k -> k < 3, xs) with
                    | Some k -> Pos(k)
                    | None -> Pos(1)"""));
    }

    @Test
    void anElementOfARangeSurvivesAConstructionThatKeepsElements() {
        assertEquals(List.of(), reported("(n: Int) -> List<Pos>", "Pos", """
                (n) = if n >= 1
                    then List.map(k -> Pos(k), List.take(2, List.rangeInclusive(1, n)))
                    else []"""));
    }

    /** The control: a range from nought has an element nothing puts above it. */
    @Test
    void anElementOfARangeFromNoughtIsNotAboveNought() {
        assertEquals(List.of("E2011"), reported("(n: Int) -> List<Pos>", "Pos", """
                (n) = if n >= 1
                    then List.map(k -> Pos(k), List.rangeInclusive(0, n))
                    else []"""));
    }

    /** The control: the range ends where its second argument does, and no earlier. */
    @Test
    void anElementOfARangeIsNotBelowItsLastArgument() {
        assertEquals(List.of("E2011"), reported("(n: Int) -> List<Small>", "Small", """
                (n) = if n >= 1 && n <= 20
                    then List.map(k -> Small(k), List.rangeInclusive(1, n))
                    else []"""));
    }

    @Test
    void anElementOfARangeIsBelowItsLastArgument() {
        assertEquals(List.of(), reported("(n: Int) -> List<Small>", "Small", """
                (n) = if n >= 1 && n <= 10
                    then List.map(k -> Small(k), List.rangeInclusive(1, n))
                    else []"""));
    }

    /** The bounds are read where the call was written. Named beforehand, the ends are values of
     * their own, and the elements are taken somewhere else. */
    @Test
    void theEndsOfARangeNamedBeforeItIsConsumedAreTheEndsItWasMadeWith() {
        assertEquals(List.of(), reported("(n: Int) -> List<Pos>", "Pos", """
                (n) = if n >= 0
                    then {
                        let lo = n + 1
                        let r = List.rangeInclusive(lo, lo + 3)
                        List.map(k -> Pos(k), r)
                    }
                    else []"""));
    }

    @Test
    void theEndsOfARangeAreReadInsideAClosureThatConsumesIt() {
        assertEquals(List.of(), reported("(ns: List<Int>) -> List<List<Pos>>", "Pos", """
                (ns) = List.map(n -> if n >= 1
                    then List.map(k -> Pos(k), List.rangeInclusive(1, n))
                    else [], ns)"""));
    }

    /** A helper that makes the range is the common way to write it. */
    @Test
    void aRangeMadeInAHelperIsReadAsTheRangeItIs() {
        assertEquals(List.of(), reported("""
                let ones (m: Int): List<Int> = List.rangeInclusive(1, m)
                """, "(n: Int) -> List<Pos>", "Pos",
                "(n) = if n >= 1 then List.map(k -> Pos(k), ones(n)) else []"));
    }

    @Test
    void aFilterMadeInAHelperIsReadAsTheFilterItIs() {
        assertEquals(List.of(), reported("""
                let nonNegative (ys: List<Int>): List<Int> = List.filter(y -> y >= 0, ys)
                """, "(xs: List<Int>) -> List<Idx>", "Idx",
                "(xs) = List.map(x -> Idx(x), nonNegative(xs))"));
    }

    /** The control: a helper that does not filter says nothing of the elements. */
    @Test
    void aHelperThatKeepsEverythingSaysNothingOfTheElements() {
        assertEquals(List.of("E2011"), reported("""
                let everything (ys: List<Int>): List<Int> = List.filter(y -> y < 10, ys)
                """, "(xs: List<Int>) -> List<Idx>", "Idx",
                "(xs) = List.map(x -> Idx(x), everything(xs))"));
    }

    /** The control: the filter keeps what is below ten, which says nothing of nought. */
    @Test
    void anElementKeptByAnotherPredicateIsNotKnownNotNegative() {
        assertEquals(List.of("E2011"), overList("List<Idx>", "Idx",
                "List.map(x -> Idx(x), List.filter(x -> x < 10, xs))"));
    }

    /** The control: a map rewrites the elements, so what held of the ones it was given does not. */
    @Test
    void whatHeldOfTheElementsBeforeAMapDoesNotHoldAfterIt() {
        assertEquals(List.of("E2011"), overList("List<Idx>", "Idx",
                "List.map(x -> Idx(x), List.map(y -> y - 1, List.filter(y -> y >= 0, xs)))"));
    }
}
