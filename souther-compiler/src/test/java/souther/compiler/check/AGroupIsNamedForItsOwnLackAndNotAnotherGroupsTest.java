package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.types.TypeName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Out of every declaration with no value, the ones worth saying so about.
 *
 * <p>Having no value spreads outwards, so most of the declarations that have none have none because
 * of one that does. What the author changes is that one, and everything else comes right when it
 * does — so the reading that decides what to say is not "which have none" but "which have none of
 * their own".
 *
 * <p>Declarations written in terms of each other are one such thing and are named together. There is
 * no first among them to blame, and a reading that picked one would pick by the order they happen to
 * be written in.
 */
class AGroupIsNamedForItsOwnLackAndNotAnotherGroupsTest {

    private static List<List<String>> reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code().toString())
                        .filter(each -> !each.equals("E1013")).toList(),
                "the model this reads has to be one somebody could write");
        return UninhabitableTypes.withNoValueOfTheirOwn(compilation.module("demo"),
                        compilation.symbols("demo"),
                        TypeCardinality.solve(compilation.module("demo"),
                                compilation.symbols("demo")))
                .stream().map(each -> each.stream().map(TypeName::name).toList()).toList();
    }

    @Test
    void nothingIsSaidOfAModelWhereEverythingHasAValue() {
        assertEquals(List.of(), reported("""
                module demo

                data Chain = { next: Chain? }
                """));
    }

    /** Two written in terms of each other, named together and once. */
    @Test
    void recordsWrittenInTermsOfEachOtherAreOneThingToSay() {
        assertEquals(List.of(List.of("A", "B")), reported("""
                module demo

                data A = { b: B }
                data B = { a: A }
                """));
    }

    /** A sum and its cases are the one recursion, however many declarations it is spread over. */
    @Test
    void aSumAndItsCasesAreOneRecursion() {
        assertEquals(List.of(List.of("Leaf", "Branch", "Shape")), reported("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """));
    }

    /** The record holding it has no value either, and nothing is the matter with it. */
    @Test
    void aRecordThatHoldsOneIsNotNamedBesideIt() {
        assertEquals(List.of(List.of("Leaf", "Branch", "Shape")), reported("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch

                data User = { shape: Shape }
                """));
    }

    /**
     * And where the group reading it has a lack of its own, both are named. Granting {@code Bad} a
     * value leaves {@code A} and {@code B} with nowhere to stop all the same, so theirs is not the
     * same lack reported twice.
     */
    @Test
    void aGroupWithALackOfItsOwnIsNamedBesideTheOneItReads() {
        assertEquals(List.of(List.of("Bad"), List.of("A", "B")), reported("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data A = { b: B }
                data B = { a: A, bad: Bad }
                """));
    }

    /**
     * One of a group having a lack of its own is not the group having one.
     *
     * <p>{@code A} cannot be built whatever else is true — its own rule about its own field says so —
     * and {@code B} has no value only because {@code A} has none and {@code Other} has none. They are
     * written in terms of each other, so they are one group until the question is asked, and the
     * answer is about the members rather than about the group: granting {@code Other} a value leaves
     * {@code A} where it was and takes {@code B} out.
     */
    @Test
    void oneMemberOfAGroupMayHaveALackTheOthersDoNot() {
        assertEquals(List.of(List.of("Other"), List.of("A")), reported("""
                module demo

                data Other = Int
                    invariant no = value >= 2 && value <= 1

                data A = { b: B, n: Int }
                    invariant no = n >= 2 && n <= 1

                data B = A | Other
                """));
    }

    /**
     * A lack reaches a set through a type that has values.
     *
     * <p>{@code MaybeBad} has one value — the absent one — because {@code Bad} has none, and one is
     * too few to fill a set of two. Nothing between them has no value, so the two groups with none
     * are not joined by anything, and a reading that asked only about what a group reads directly
     * would call the set's lack its own. Give {@code Bad} a value and the set fills itself.
     */
    @Test
    void aLackReachingASetThroughATypeThatHasValuesIsStillTheLackOfTheFirst() {
        assertEquals(List.of(List.of("Bad")), reported("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data MaybeBad = { x: Bad? }

                data NeedTwo = Set<MaybeBad>
                    invariant two = Set.size(value) >= 2
                """));
    }

    /**
     * And where the lack travels through a value-bearing member of the very group it is asked of.
     *
     * <p>{@code A}, {@code B} and {@code C} are answered together, and {@code B} has a value because
     * an absent one is a value. So granting what the group reads changes nothing — it reads nothing
     * outside itself — and both {@code A} and {@code C} are left with none. They are not one thing to
     * say: grant {@code A} and {@code C} comes right, which is only found by asking again once the
     * two have been told apart.
     */
    @Test
    void aLackTravellingThroughAValueBearingMemberOfItsOwnGroupIsStillTheFirstsLack() {
        assertEquals(List.of(List.of("A")), reported("""
                module demo

                data A = { b: B, n: Int }
                    invariant no = n >= 2 && n <= 1

                data B = { c: C? }

                data C = { a: A }
                """));
    }

    /** A set that cannot be filled is its own group, its element having a value of its own. */
    @Test
    void aSetThatCannotBeFilledIsNamedAndItsElementIsNot() {
        assertEquals(List.of(List.of("Pair")), reported("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                """));
    }

    @Test
    void aNameWhoseValueIsANonEmptyCollectionOfItselfIsNamedAlone() {
        assertEquals(List.of(List.of("Nest")), reported("""
                module demo

                data Nest = List<Nest>
                    invariant someNest = List.length(value) >= 1
                """));
    }
}
