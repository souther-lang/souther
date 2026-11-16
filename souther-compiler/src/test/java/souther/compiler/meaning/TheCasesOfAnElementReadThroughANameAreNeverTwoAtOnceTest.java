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
 * An element of a container read through a name is one value wherever the name is read, so the
 * cases it is are never two at once, and where a line decides is taken apart on the case it is and
 * not on what the other cases would have asked.
 *
 * <p>A statement that walks a chain of candidates under one case of the element and another chain
 * under another has a line decide in each case where its own chain says so. Were the element's
 * cases left free of each other, the line would decide in a way for every pair of ways the two
 * chains come out, and a chain would be asked in the case that does not walk it.
 */
class TheCasesOfAnElementReadThroughANameAreNeverTwoAtOnceTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");

    private static final int CHAIN = 3;

    private static Proposition.Compared line() {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x"))),
                        ExactRatio.ONE)), Rel.GT), true);
    }

    private static Proposition truth(String name) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(name)), true);
    }

    /** The element of {@code rules} being {@code leaf}, read through a name where {@code named}. */
    private static Proposition is(String leaf, boolean named) {
        DecisionSubject.AnInput element = named
                ? new DecisionSubject.AnInput(TermPath.of("rules").element(),
                        new ValueIdentity.OfAnElement(new BindingId(OWNER, 4)))
                : new DecisionSubject.AnInput(TermPath.of("rules").element());
        return new Proposition.InCases(element, CasesLeft.ofEach(List.of(Refinement.of(
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
    private static List<List<Proposition>> casesOfTheLine(boolean named) {
        Proposition stated = Proposition.any(List.of(
                Proposition.all(List.of(is("A", named), line())),
                Proposition.all(List.of(is("B", named), chain("b"), line())),
                Proposition.all(List.of(is("C", named), chain("c"), line()))));
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
    @Test
    void aCaseAsksTheChainOfTheCaseTheElementIsAndNoOther() {
        List<List<Proposition>> cases = casesOfTheLine(true);

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

    /** Read through no name, two parts asking the cases of an element may ask it of two elements,
     *  and the cases may be two at once: a chain is asked beside the element being the other. */
    @Test
    void anElementReadThroughNoNameMayBeTwoCasesAtOnce() {
        List<List<Proposition>> cases = casesOfTheLine(false);

        assertTrue(cases.stream().anyMatch(one -> isTheCase(one, "C") && asksChain(one, "b")),
                "C asks a chain of B");
    }
}
