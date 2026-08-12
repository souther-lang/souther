package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Types with no value, refused whatever left them without one.
 *
 * <p>These were admitted for as long as the reading was a walk looking for a recursion with nowhere
 * to stop. Each of them has no value for a reason a walk has no place for — a sum needs an answer
 * about every case at once, a set needs its element counted, rules that contradict need no walking at
 * all — and each was a separate gap for as long as the shape rather than the count was what was read.
 *
 * <p>They are one thing now. What is asked of every declaration is how many values it has, and every
 * model here is one whose answer is none.
 *
 * <p>Each is written beside the nearest model that does have a value, so what is asserted is the
 * reading that told them apart and not merely that something was refused.
 */
class ATypeWithNoValueIsRefusedHoweverItCameToHaveNoneTest {

    private static List<String> codesFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .map(diagnostic -> diagnostic.code())
                .toList();
    }

    private static void refuses(String data, String source) {
        assertEquals(List.of("E1013"), codesFor(source), "`" + data + "` has no value to be built");
    }

    private static void admits(String source) {
        assertEquals(List.of(), codesFor(source), "a value of this can be written");
    }

    /**
     * A sum is where a recursion may stop, in a case the one running did not come through. Where
     * every case holds the sum there is no such case, and the answer is the disjunction over all of
     * them rather than anything on the way to one.
     */
    @Test
    void aSumWhoseEveryCaseHoldsTheSumIsRefused() {
        refuses("Shape", """
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """);
    }

    /** And one case that stops is all it takes for every one of them to have a value. */
    @Test
    void aSumWithOneCaseThatStopsIsAdmitted() {
        admits("""
                module demo

                data Leaf = { n: Int }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """);
    }

    /** And where the recursion leaves through a record and comes back through the sum. */
    @Test
    void aCycleRoutedThroughASumIsRefused() {
        refuses("Leaf", """
                module demo

                data Leaf = { t: Trunk }
                data Branch = { t: Trunk }
                data Shape = Leaf | Branch

                data Trunk = { s: Shape }
                """);
    }

    /**
     * A set of two needs two values of its element that differ. Nothing recurses here: what refuses
     * it is one count against another.
     */
    @Test
    void aSetAskingForMoreValuesThanItsElementHasIsRefused() {
        refuses("Pair", """
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                """);
    }

    /** The same set over an element with two values, which fills. */
    @Test
    void aSetItsElementCanFillIsAdmitted() {
        admits("""
                module demo

                data Two = Int
                    invariant only = value >= 1 && value <= 2

                data Pair = Set<Two>
                    invariant two = Set.size(value) >= 2
                """);
    }

    /** A list holds a value over again, so one value fills a list of any length. */
    @Test
    void aListAskingForMoreThanItsElementHasIsAdmitted() {
        admits("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Many = List<One>
                    invariant two = List.length(value) >= 2
                """);
    }

    /** Rules that cannot all hold, which needs no walking anywhere. */
    @Test
    void aNumberBoundedBothWaysPastItselfIsRefused() {
        refuses("Bad", """
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                """);
    }

    /**
     * And where the two ends are two rules rather than one.
     *
     * <p>A report used to be asked what it made of this: both ends of the range the rules describe
     * are values nobody writes, and counting either as a measurement waiting for a row was the
     * mistake. Nothing reaches a report now — the type is refused where it is declared, and a line
     * at a value of it is a line in a model that does not compile.
     */
    @Test
    void twoRulesThatCannotBothHoldAreRefused() {
        refuses("Impossible", """
                module demo

                data Impossible = Int
                    invariant low = value >= 10
                    invariant high = value <= 0
                """);
    }

    /**
     * And where the contradiction is about a number a field away rather than the value itself.
     *
     * <p>This was a fixture: a case of a sum nothing could compose a value for, which is what a
     * generator is asked about. It is refused before a generator sees it now, and what it stood for
     * there has to be a type that has values the search cannot reach.
     */
    @Test
    void aFieldsNumberBoundedBothWaysPastItselfIsRefused() {
        refuses("Card", """
                module demo

                data Amount = Decimal
                    invariant value >= 0.0m

                data Card = { holder: Amount }
                    invariant impossible = holder.value >= 10.0m && holder.value <= 5.0m
                """);
    }

    /** The same record with a rule its field's range leaves room for. */
    @Test
    void aFieldsNumberBoundedWithinItselfIsAdmitted() {
        admits("""
                module demo

                data Amount = Decimal
                    invariant value >= 0.0m

                data Card = { holder: Amount }
                    invariant priced = holder.value >= 5.0m && holder.value <= 10.0m
                """);
    }

    @Test
    void aNumberWithOneValueLeftIsAdmitted() {
        admits("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1
                """);
    }

    /**
     * Said once for the group and not for everything downstream of it. The record here has no value
     * either, and nothing about it is what the author has to change.
     */
    @Test
    void aRecordHoldingOneIsNotReportedBesideIt() {
        refuses("Leaf", """
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch

                data User = { shape: Shape }
                """);
    }

    /** And where one of two written in terms of each other has a rule of its own that leaves it
     * nothing, that one is said and the other, which was answering for it, is not. */
    @Test
    void oneOfTwoWrittenInTermsOfEachOtherIsReportedWhereOnlyItHasARuleOfItsOwn() {
        assertEquals(List.of("E1013", "E1013"), codesFor("""
                module demo

                data Other = Int
                    invariant no = value >= 2 && value <= 1

                data A = { b: B, n: Int }
                    invariant no = n >= 2 && n <= 1

                data B = A | Other
                """), "`Other` and `A`, and not `B` beside them");
    }

    /**
     * A lack that reaches a set through a type with values is still the first one's.
     *
     * <p>Nothing between them has no value — a record holding an absent value has one — so there is
     * no edge from one to the other to follow. What settles it is granting the first a value and
     * finding the set fills itself.
     */
    @Test
    void aSetTooSmallBecauseOfSomethingElseIsNotReportedBesideIt() {
        refuses("Bad", """
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data MaybeBad = { x: Bad? }

                data NeedTwo = Set<MaybeBad>
                    invariant two = Set.size(value) >= 2
                """);
    }

    /** And where the set is too small on its own, with nothing granted to change it. */
    @Test
    void aSetTooSmallOnItsOwnIsReported() {
        refuses("Pair", """
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Held = { x: One? }

                data Pair = Set<Held>
                    invariant three = Set.size(value) >= 3
                """);
    }

    /** And where the group reading it has nowhere to stop of its own, both are said. */
    @Test
    void aGroupWithNoValueOfItsOwnIsReportedBesideTheOneItReads() {
        assertEquals(List.of("E1013", "E1013"), codesFor("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data A = { b: B }
                data B = { a: A, bad: Bad }
                """), "granting `Bad` a value leaves `A` and `B` where they were");
    }
}
