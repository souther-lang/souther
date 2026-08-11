package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a data that needs a value of itself has anywhere to stop.
 *
 * <p>A recursion bottoms out where an occurrence has a value that holds no further one. An optional
 * always has one and the language keeps it that way — a newtype may not wrap an optional, so there
 * is nowhere to write a rule that takes {@code None} away. A collection's empty value is not held
 * like that: it is there only while the rules admit it, and a rule on how much the collection holds
 * takes it away. So the two are not one base case, and which of them an occurrence is has to be read
 * rather than seen in the shape of the type.
 *
 * <p>Each model here differs from its neighbour in one thing, so that what is asserted is which
 * reading the walk made and not merely that it reached an answer.
 */
class ACollectionBottomsOutOnlyWhereItMayBeEmptyTest {

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
        List<String> codes = codesFor(source);
        assertEquals(List.of("E1013"), codes, "`" + data + "` has no value to be built");
    }

    private static void admits(String source) {
        assertEquals(List.of(), codesFor(source), "a value of this can be written");
    }

    // ---- a recursion through a collection the rules will not let be empty ------------------------

    /**
     * The floor is read at the name the field is written with, before what that name wraps is
     * reached. Read after the unwrapping instead, the list is a bare {@code List<Tree>} whose own
     * rules say nothing, and every tree is admitted a value it has no way to build.
     */
    @Test
    void aFloorOnTheNameAFieldWearsReachesWhatTheNameWraps() {
        refuses("Tree", """
                module demo

                data Kids = List<Tree>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /**
     * A count rule cannot be stated on a name over another name. {@code value} there is the inner
     * newtype, not the list it wraps, so {@code List.length} has nothing to count. Held because it is
     * why there is no case here of a floor written above the name that wraps the collection: the
     * one-name step is the whole of what carrying a floor across a name ever has to do.
     */
    @Test
    void aCountRuleIsWrittenOnTheNameThatWrapsTheCollection() {
        assertTrue(codesFor("""
                module demo

                data Kids = Inner
                    invariant nonEmpty = List.length(value) >= 1

                data Inner = List<Tree>

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """).contains("E1317"), "the rule has nothing to count where it is written");
    }

    /** And where a layer below states it, which the name the field is written with reaches through. */
    @Test
    void aFloorUnderANameIsStillTheFieldsFloor() {
        refuses("Tree", """
                module demo

                data Kids = Inner

                data Inner = List<Tree>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** The record that has the field is the other thing that can say how much it holds, and a list
     * written out at the field has no name of its own for the rule to be written on. */
    @Test
    void theRecordsOwnRuleAboutAFieldIsAFloorThere() {
        refuses("Tree", """
                module demo

                data Tree =
                    { kids: List<Tree>
                    , v: Int
                    }
                    invariant nonEmpty = List.length(kids) >= 1
                """);
    }

    /** A cycle that leaves the collection's element and comes back through a record of its own. The
     * element is where one value stops and the next starts, and the walk has to enter it as a value
     * with fields rather than stop at having arrived. */
    @Test
    void aCycleClosingThroughARecordUnderTheCollectionIsStillACycle() {
        refuses("A", """
                module demo

                data Bs = List<B>
                    invariant nonEmpty = List.length(value) >= 1

                data A = { bs: Bs }

                data B = { a: A }
                """);
    }

    /**
     * The shortest cycle there is: a name whose value is a collection of that same name, which the
     * rules will not let be empty.
     *
     * <p>Two things meet here. The floor is written on {@code Nest} about what {@code Nest} holds, so
     * a walk beginning at the field inside reads a bare {@code List<Nest>} and finds none — the walk
     * has to begin at the name. And the element it then reaches is {@code Nest} again, so a walk
     * treating each element as a fresh start with no memory of where it has been descends forever
     * rather than answering.
     */
    @Test
    void aNameWhoseValueIsANonEmptyCollectionOfItselfIsRefused() {
        refuses("Nest", """
                module demo

                data Nest = List<Nest>
                    invariant someNest = List.length(value) >= 1
                """);
    }

    /** And the same shape where the collection may be empty, which is an ordinary tree. */
    @Test
    void aNameWhoseValueIsACollectionOfItselfBottomsOutAtTheEmptyOne() {
        admits("""
                module demo

                data Nest = List<Nest>
                """);
    }

    /** A set counts what it holds under its own name, and a floor on it is the same floor. */
    @Test
    void aSetsSizeIsAFloorOnWhatItHolds() {
        refuses("Tree", """
                module demo

                data Kids = Set<Tree>
                    invariant nonEmpty = Set.size(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** A map holds its values under a floor on its entries. Its keys are strings at a field, so what
     * a recursion can reach through one is the value side and only that. */
    @Test
    void aMapsSizeIsAFloorOnTheValuesItHolds() {
        refuses("Tree", """
                module demo

                data Kids = Map<String, Tree>
                    invariant nonEmpty = Map.size(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** A rule the range stops short of asks for the next count up: one is what meets `> 0`, and a
     * reader dropping which end it was handed reads a floor of none. */
    @Test
    void aRuleTheRangeStopsShortOfIsStillAFloor() {
        refuses("Tree", """
                module demo

                data Kids = List<Tree>
                    invariant nonEmpty = List.length(value) > 0

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    // ---- and where something can still be empty --------------------------------------------------

    /**
     * An optional is a base case whatever it holds. The name under it carries a floor, so a walk
     * peeling the occurrence off to find the reference underneath reads that floor and refuses a tree
     * that can plainly be written: the one whose {@code kids} is absent.
     */
    @Test
    void anOptionalIsReadBeforeWhatItHolds() {
        admits("""
                module demo

                data Kids = List<Tree>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids?
                    , v: Int
                    }
                """);
    }

    /**
     * An optional standing as a collection's element is not a position the language has. Held here
     * because the walk would otherwise be owed an answer for it: whether a floored collection of
     * optionals bottoms out is a question nothing can ask, and a row asserting either answer would be
     * asserting something about a program that cannot be written.
     */
    @Test
    void anOptionalIsNotAPositionInsideACollection() {
        assertEquals(List.of("E2308"), codesFor("""
                module demo

                data Kids = List<Tree?>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """));
    }

    /**
     * The floor is on the outer list and the inner one is a value of its own, which the rules say
     * nothing about. A walk carrying the count from the outer list into the inner one refuses a tree
     * whose {@code kids} is one empty list.
     */
    @Test
    void aFloorIsNotCarriedIntoWhatACollectionHolds() {
        admits("""
                module demo

                data Kids = List<List<Tree>>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** A rule that admits the empty collection is no floor. */
    @Test
    void aRuleAtZeroLeavesTheEmptyCollectionWhereItWas() {
        admits("""
                module demo

                data Kids = List<Tree>
                    invariant any = List.length(value) >= 0

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** And a rule about how much a collection may hold says nothing about how little. */
    @Test
    void aCapOnACollectionIsNotAFloorUnderIt() {
        admits("""
                module demo

                data Kids = List<Tree>
                    invariant atMostThree = List.length(value) <= 3

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                """);
    }

    /** A collection that cannot be empty is an ordinary thing to write. What is refused is a cycle
     * with nowhere to stop, and this one stops at the optional beside it. */
    @Test
    void aCollectionThatCannotBeEmptyIsNotItselfTheProblem() {
        admits("""
                module demo

                data Names = List<String>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { names: Names
                    , kid: Tree?
                    }
                """);
    }

    /** The two readings the walk has of one field, where both speak. Neither alone would refuse this
     * for the right reason, and the higher of them is what the construction has to meet. */
    @Test
    void aFieldWhoseTypeAndRecordBothSpeakTakesTheHigherFloor() {
        refuses("Tree", """
                module demo

                data Kids = List<Tree>
                    invariant nonEmpty = List.length(value) >= 1

                data Tree =
                    { kids: Kids
                    , v: Int
                    }
                    invariant atLeastTwo = List.length(kids.value) >= 2
                """);
    }

    /** A plain list bottoms out at the empty one, which is what E1013 has always said. */
    @Test
    void aPlainCollectionStillBottomsOut() {
        admits("""
                module demo

                data Tree =
                    { kids: List<Tree>
                    , v: Int
                    }
                """);
    }

    /** As does an optional with no rule anywhere near it. */
    @Test
    void anOptionalStillBottomsOut() {
        admits("""
                module demo

                data Tree =
                    { kid: Tree?
                    , v: Int
                    }
                """);
    }

    /** And a mandatory reference to itself still has nowhere to stop. */
    @Test
    void aMandatoryReferenceToItselfIsStillRefused() {
        List<String> codes = codesFor("""
                module demo

                data Tree =
                    { kid: Tree
                    , v: Int
                    }
                """);
        assertTrue(codes.contains("E1013"), "still the case the check was written for: " + codes);
    }
}
