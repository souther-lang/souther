package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two statements that are the same but for the names of the values they are about say so whether
 * or not the answers of operations inside them are held once and shared, or made again as equal
 * ones: what a statement says is what it is made of, and not how many objects it is made with.
 */
class WhatAStatementSaysUpToTheNamesDoesNotDependOnWhatIsSharedTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");

    private static final ValueName.Stdlib NEGATE = ValueName.Stdlib.operation("Int", "negate");

    private static final ValueName.Stdlib FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static DecisionAtom.OfTheInput input(String field, int name) {
        return new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(TermPath.of("i").then(field)),
                new ValueIdentity.OfAnElement(new BindingId(OWNER, name)));
    }

    private static Proposition about(Quantity quantity) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.of(0),
                Map.of(quantity, ExactRatio.ONE)), Rel.GT), true);
    }

    private static Quantity answer(ValueName.Stdlib operation, Quantity... of) {
        return new Quantity.WhatAnOperationAnswers(operation, List.of(of));
    }

    /** {@code floorMod(negate(x), negate(x))}, the answer of the negation held once. */
    private static Proposition shared(int name) {
        Quantity negated = answer(NEGATE, input("x", name));
        return about(answer(FLOOR_MOD, negated, negated));
    }

    /** The same, the answer of the negation made twice. */
    private static Proposition made(int name) {
        return about(answer(FLOOR_MOD, answer(NEGATE, input("x", name)),
                answer(NEGATE, input("x", name))));
    }

    @Test
    void aStatementIsTheSameUpToTheNamesWhetherItsAnswersAreSharedOrMadeTwice() {
        assertEquals(shared(0), shared(0));
        assertTrue(ReadThroughNames.sameUpToTheNames(shared(0), shared(1)));
        assertTrue(ReadThroughNames.sameUpToTheNames(made(0), made(1)));
        assertTrue(ReadThroughNames.sameUpToTheNames(shared(0), made(1)),
                "one with the answer held once is the other with it made twice");
        assertTrue(ReadThroughNames.sameUpToTheNames(made(0), shared(1)));
    }

    /** Some element of the container {@code c}, the value named {@code name}, is true. A
     *  quantifier is not made one for equal ones, as a conjunction is. */
    private static Proposition someElement(int name) {
        return new Proposition.Some(new DecisionSubject.AnInput(TermPath.of("c"),
                new ValueIdentity.OfAnElement(new BindingId(OWNER, name))),
                new Proposition.Truth(new DecisionSubject.AnInput(
                        TermPath.of("c").element().then("x"), ValueIdentity.AT_THE_POSITION),
                        true), true);
    }

    /** A statement that holds a part twice: beside itself, and inside a disjunction. */
    private static Proposition holdingAPartTwice(Proposition one, Proposition other,
                                                 Proposition beside) {
        return Proposition.all(List.of(one, Proposition.any(List.of(other, beside))));
    }

    @Test
    void aStatementIsTheSameUpToTheNamesWhetherItsPartsAreSharedOrMadeTwice() {
        Proposition beside = new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of("i").then("y"), ValueIdentity.AT_THE_POSITION), true);
        Proposition part = someElement(0);
        Proposition shared = holdingAPartTwice(part, part, beside);
        // The same value as the part, held by another object.
        Proposition twice = holdingAPartTwice(someElement(1), someElement(1), beside);

        assertTrue(ReadThroughNames.sameUpToTheNames(shared, twice),
                "a part held by one object is the part held by two equal ones");
        assertTrue(ReadThroughNames.sameUpToTheNames(twice, shared));
    }

    @Test
    void twoValuesAtOnePlaceAreStillTwoValues() {
        Proposition one = about(answer(FLOOR_MOD, answer(NEGATE, input("x", 0)),
                answer(NEGATE, input("x", 1))));
        assertFalse(ReadThroughNames.sameUpToTheNames(one, shared(2)));
        assertFalse(ReadThroughNames.sameUpToTheNames(shared(2), one));
    }
}
