package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Cardinality;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every declaration a module reaches, answered together.
 *
 * <p>A value is built, so the reading grants nothing and grants a value only where one is shown. What
 * that decides is the recursions: a type written in terms of itself with nowhere to stop is one no
 * building finishes, and it is the granting-nothing that leaves it there rather than any walk looking
 * for a cycle. A case that stops is all it takes for the whole recursion to be granted one.
 *
 * <p>And the counting is what decides the rest. A set cannot hold more values of its element than the
 * element has, which is a comparison of two numbers rather than a shape anything can be seen in.
 */
class ATypeIsGrantedAValueOnlyWhereOneIsShownTest {

    private static Map<String, Cardinality> solved(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        // Everything but the check this replaces: a model refused for some other reason is one whose
        // rules were never read, and every row of it would answer from the absence of them.
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code().toString())
                        .filter(each -> !each.equals("E1013")).toList(),
                "the model this reads has to be one somebody could write");
        Map<TypeSymbol, Cardinality> solution =
                TypeCardinality.solve(compilation.module("demo").defs().stream().map(Derived.Def::read).toList(), compilation.symbols("demo")).all();
        Map<String, Cardinality> byName = new LinkedHashMap<>();
        solution.forEach((name, each) -> byName.put(name.name(), each));
        return byName;
    }

    private static void hasNoValue(String source, String... names) {
        Map<String, Cardinality> solved = solved(source);
        for (String each : names) {
            assertEquals(Cardinality.NO_VALUE, solved.get(each), each + " has no value");
        }
    }

    private static void hasAValue(String source, String... names) {
        Map<String, Cardinality> solved = solved(source);
        for (String each : names) {
            assertFalse(solved.get(each).none(), each + " has one");
        }
    }

    @Test
    void twoRecordsWrittenInTermsOfEachOtherHaveNoValue() {
        hasNoValue("""
                module demo

                data A = { b: B }
                data B = { a: A }
                """, "A", "B");
    }

    @Test
    void aSumWhoseEveryCaseHoldsTheSumHasNoValue() {
        hasNoValue("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """, "Leaf", "Branch", "Shape");
    }

    @Test
    void aCycleRoutedThroughASumHasNoValueEither() {
        hasNoValue("""
                module demo

                data Leaf = { t: Trunk }
                data Branch = { t: Trunk }
                data Shape = Leaf | Branch

                data Trunk = { s: Shape }
                """, "Leaf", "Branch", "Shape", "Trunk");
    }

    /** One case that stops is all the recursion needs. */
    @Test
    void aSumWithACaseThatStopsIsGrantedAValue() {
        hasAValue("""
                module demo

                data Leaf = { n: Int }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """, "Leaf", "Branch", "Shape");
    }

    @Test
    void aRecordHoldingSomethingWithNoValueHasNone() {
        hasNoValue("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch

                data User = { shape: Shape }
                """, "User");
    }

    @Test
    void aNameWhoseValueIsANonEmptyCollectionOfItselfHasNoValue() {
        hasNoValue("""
                module demo

                data Nest = List<Nest>
                    invariant someNest = List.length(value) >= 1
                """, "Nest");
    }

    /** And the same shape where the collection may be empty, which is where it stops. */
    @Test
    void aNameWhoseValueIsACollectionOfItselfStopsAtTheEmptyOne() {
        hasAValue("""
                module demo

                data Nest = List<Nest>
                """, "Nest");
    }

    /** A `None` is where it stops, so a recursion through one is granted a value. */
    @Test
    void aRecursionThroughAnOptionalStopsAtNone() {
        hasAValue("""
                module demo

                data Chain = { next: Chain? }
                """, "Chain");
    }

    @Test
    void aSetAskingForMoreValuesThanItsElementHasHasNone() {
        hasNoValue("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                """, "Pair");
    }

    /**
     * The same set over an element with two values, which fills. Told apart from the one above by the
     * element's rules and nothing else.
     */
    @Test
    void aSetAskingForNoMoreThanItsElementHasIsFilled() {
        hasAValue("""
                module demo

                data Two = Int
                    invariant only = value >= 1 && value <= 2

                data Pair = Set<Two>
                    invariant two = Set.size(value) >= 2
                """, "Pair");
    }

    /**
     * Where the count arrives through a sum of two singletons. Nothing recurses here, so every answer
     * is the number it is: rounded to the counts some rule asks about, the two cases would come to
     * more than anything asks and the set could not be told it is too small.
     */
    @Test
    void aCountReachingASetThroughASumIsNotRoundedAway() {
        hasNoValue("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Two = Int
                    invariant only = value >= 2 && value <= 2

                data Choice = One | Two

                data Three = Set<Choice>
                    invariant three = Set.size(value) >= 3
                """, "Three");
    }

    /** And where the count arrives through a set of a set. */
    @Test
    void aCountReachingASetThroughASetIsCountedToo() {
        hasNoValue("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Single = Set<One>
                    invariant one = Set.size(value) == 1

                data Pair = Set<Single>
                    invariant two = Set.size(value) >= 2
                """, "Pair");
    }

    /** A list holds a value over again, so the same element fills one however long it must be. */
    @Test
    void aListAskingForMoreThanItsElementHasIsStillFilled() {
        hasAValue("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Many = List<One>
                    invariant two = List.length(value) >= 2
                """, "Many");
    }

    @Test
    void rulesThatCannotAllHoldLeaveNoValue() {
        hasNoValue("""
                module demo

                data Bad = Int
                    invariant no = value >= 2 && value <= 1
                """, "Bad");
    }
}
