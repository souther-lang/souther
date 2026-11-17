package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases of a value at an element of a container are never two at once where the statement
 * holds one value at that position, and where a line decides is taken apart on the case the value
 * is and not on what the other cases would have asked.
 *
 * <p>A statement that walks a chain of candidates under one case of the value and another chain
 * under another has a line decide in each case where its own chain says so. Were the cases left
 * free of each other, the line would decide in a way for every pair of ways the two chains come
 * out, and a chain would be asked in the case that does not walk it. A statement about two
 * elements of the container holds two values at the position, and then one element may be one
 * case while the other is another.
 */
class TheCasesOfOneValueAtAnElementOfAStatementAreNeverTwoAtOnceTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");

    private static final int CHAIN = 3;

    /** How the statement reads the element of {@code rules}. */
    private enum Reads {
        /** Every part through the one name the element was given. */
        ONE_NAME,
        /** Every part through no name: the one element the statement is about. */
        NO_NAME,
        /** The cases of {@code B} through one name, the others through another: two elements. */
        TWO_NAMES,
        /** {@code B} and {@code C} through no name, and {@code A} through a name: the statement
         *  holds two values at the position, and which of them the unnamed two are is not said. */
        NO_NAME_BESIDE_A_NAME
    }

    private static Proposition.Compared line() {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x"))),
                        ExactRatio.ONE)), Rel.GT), true);
    }

    private static Proposition truth(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    private static ValueIdentity named(int ordinal) {
        return new ValueIdentity.OfAnElement(new BindingId(OWNER, ordinal));
    }

    /** The element of {@code rules} being {@code leaf}, read as {@code reads} says. */
    private static Proposition is(String leaf, Reads reads) {
        TermPath element = TermPath.of("rules").element();
        DecisionSubject.AnInput subject = switch (reads) {
            case ONE_NAME -> new DecisionSubject.AnInput(element, named(4));
            case NO_NAME -> new DecisionSubject.AnInput(element);
            case TWO_NAMES -> new DecisionSubject.AnInput(element,
                    named(leaf.equals("B") ? 4 : 5));
            case NO_NAME_BESIDE_A_NAME -> leaf.equals("A")
                    ? new DecisionSubject.AnInput(element, named(7))
                    : new DecisionSubject.AnInput(element);
        };
        return new Proposition.InCases(subject, CasesLeft.ofEach(List.of(Refinement.of(
                new Case.SumCase(TypeSymbols.declared(new TypeKey("probe", leaf)), true)))), true);
    }

    private static Proposition chain(String prefix) {
        List<Proposition> each = new ArrayList<>();
        for (int i = 1; i <= CHAIN; i++) {
            each.add(truth(prefix + i));
        }
        return Proposition.any(each);
    }

    /** Every case where the line decides, as the parts each asks: where the element is {@code A},
     *  or {@code B} with one of {@code b1..b3} holding, or {@code C} with one of {@code c1..c3}. */
    private static List<List<Proposition>> casesOfTheLine(Reads reads) {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(is("A", reads), line())),
                Proposition.all(List.of(is("B", reads), chain("b"), line())),
                Proposition.all(List.of(is("C", reads), chain("c"), line()))));
        List<WhereEachLineDecides.Decides> lines = WhereEachLineDecides.in(stated, term -> false);
        assertEquals(1, lines.size(), "one relation is a line");
        List<List<Proposition>> out = new ArrayList<>();
        for (DecidingCase one : lines.getFirst().cases()) {
            for (Proposition leaf : DecidingCases.eachOf(one.standsFor())) {
                out.add(leaf instanceof Proposition.All all ? all.parts() : List.of(leaf));
            }
        }
        return out;
    }

    /** Whether the case holds the element to be {@code leaf}. */
    private static boolean isTheCase(List<Proposition> asked, String leaf) {
        return asked.stream().anyMatch(part -> part instanceof Proposition.InCases in && in.holds()
                && String.valueOf(in.spelling()).endsWith("is " + leaf));
    }

    /** Whether the case asks a truth of the chain {@code prefix} names. */
    private static boolean asksChain(List<Proposition> asked, String prefix) {
        return asked.stream().anyMatch(part -> part instanceof Proposition.Truth truth
                && String.valueOf(truth.of()).contains(prefix));
    }

    /** A case for the element being {@code A}, and one for each way a chain comes out in each of
     *  the others: a line is taken apart on its own chain. */
    private static void assertEachCaseAsksOnlyItsOwnChain(Reads reads) {
        List<List<Proposition>> cases = casesOfTheLine(reads);

        assertEquals(1 + 2 * CHAIN, cases.size(), "a way for each of the chains");
        for (List<Proposition> one : cases) {
            if (isTheCase(one, "B")) {
                assertFalse(asksChain(one, "c"), "B walks no chain of C");
            }
            if (isTheCase(one, "C")) {
                assertFalse(asksChain(one, "b"), "C walks no chain of B");
            }
            if (isTheCase(one, "A")) {
                assertFalse(asksChain(one, "b") || asksChain(one, "c"), "A walks no chain");
            }
        }
    }

    @Test
    void anElementReadThroughOneNameAsksTheChainOfItsOwnCaseAlone() {
        assertEachCaseAsksOnlyItsOwnChain(Reads.ONE_NAME);
    }

    /** A statement that reads the element through no name holds one value at its position. */
    @Test
    void anElementReadThroughNoNameIsOneValueWhereTheStatementHoldsOne() {
        assertEachCaseAsksOnlyItsOwnChain(Reads.NO_NAME);
    }

    /** Two names at one position are two elements: one may be {@code C} while the other is
     *  {@code B}, and a chain of B is asked beside the cases of C. */
    @Test
    void twoElementsOfTheContainerMayBeTwoCasesAtOnce() {
        List<List<Proposition>> cases = casesOfTheLine(Reads.TWO_NAMES);

        assertTrue(cases.stream().anyMatch(one -> isTheCase(one, "C") && asksChain(one, "b")),
                "C asks a chain of B");
    }

    /** Where a name stands beside them at the position, parts read through no name are not shown
     *  to be of one element, and are left free of each other. */
    @Test
    void partsReadThroughNoNameBesideANamedOneAreLeftFreeOfEachOther() {
        List<List<Proposition>> cases = casesOfTheLine(Reads.NO_NAME_BESIDE_A_NAME);

        assertTrue(cases.stream().anyMatch(one -> isTheCase(one, "C") && asksChain(one, "b")),
                "C asks a chain of B");
    }
}
