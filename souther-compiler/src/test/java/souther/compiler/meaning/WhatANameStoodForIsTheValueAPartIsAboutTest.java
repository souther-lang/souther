package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a statement is told of the names it was read through ({@link ReadThroughNames}), asked of
 * statements written out here: a number and a truth at an element of {@code x.items} and a number
 * of the row, {@code x.gate}, with {@code a} and {@code b} two names for elements of the items.
 */
class WhatANameStoodForIsTheValueAPartIsAboutTest {

    private static final TermPath ITEMS = TermPath.of("x").then("items");
    private static final TermPath N = ITEMS.element().then("n");
    private static final TermPath PAID = ITEMS.element().then("paid");
    private static final TermPath GATE = TermPath.of("x").then("gate");

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static final ElementsNamed.Slot AN_ITEM = new ElementsNamed.Slot(
            new InputReads.ContainerOf.AtAPosition(ITEMS), HeldIn.Part.ELEMENT);

    /** What stands for a part read through two names for one element. */
    private static final Proposition TWO_AS_ONE = new Proposition.Unread(Optional.empty(), 0,
            new WhyUnread.TwoElementsOfOneContainer(), false, true);

    private static ElementsNamed named(BindingId... names) {
        return ElementsNamed.of(List.of(names).stream()
                .map(name -> new ElementsNamed.Named(AN_ITEM, name)).toList());
    }

    private static DecisionAtom.OfTheInput number(TermPath at, ValueIdentity identity) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(at), identity);
    }

    /** {@code at < 0}, of the value {@code identity} says: {@code at >= 0} not holding. */
    private static Proposition below(TermPath at, ValueIdentity identity) {
        return Proposition.compared(new Relation.Affine(
                LinearForm.atomMinusConstant(number(at, identity), ExactRatio.ZERO), Rel.GE),
                false);
    }

    private static Proposition truth(TermPath at, ValueIdentity identity) {
        return new Proposition.Truth(new DecisionSubject.AnInput(at, identity), true);
    }

    private static ValueIdentity of(BindingId name) {
        return new ValueIdentity.OfAnElement(name);
    }

    private static Proposition readThrough(Proposition stated, ElementsNamed names) {
        return ReadThroughNames.readThrough(stated, names, () -> TWO_AS_ONE);
    }

    /** A number and a truth at the element are told the one name that stood for it; the row's
     *  number is told nothing. */
    @Test
    void whatIsAtTheElementIsToldTheNameThatStoodForIt() {
        Proposition stated = Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                truth(PAID, ValueIdentity.AT_THE_POSITION),
                below(GATE, ValueIdentity.AT_THE_POSITION)));
        assertEquals(Proposition.all(List.of(below(N, of(A)), truth(PAID, of(A)),
                        below(GATE, ValueIdentity.AT_THE_POSITION))),
                readThrough(stated, named(A)));
    }

    /**
     * Where two names stood for the element, what is at it is a part nothing read, and the rest is
     * what it was: neither true nor false is put in its place.
     */
    @Test
    void aPartAtAnElementTwoNamesStoodForIsUnreadAndTheRestStays() {
        Proposition stated = Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                below(GATE, ValueIdentity.AT_THE_POSITION)));
        assertEquals(Proposition.all(List.of(TWO_AS_ONE, below(GATE, ValueIdentity.AT_THE_POSITION))),
                readThrough(stated, named(A, B)));
    }

    /** Two numbers of a form told to be one number are no form, and the form is unread. */
    @Test
    void twoNumbersOfAFormToldIntoOneAreUnread() {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(number(N, of(A)), ExactRatio.ONE.negated());
        coefs.put(number(N, ValueIdentity.AT_THE_POSITION), ExactRatio.ONE);
        Proposition stated = Proposition.compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.ZERO, coefs), Rel.GE), false);
        assertSame(TWO_AS_ONE, readThrough(stated, named(A)));
    }

    /** A statement none of whose parts is told anything is the statement it was. */
    @Test
    void aStatementNothingIsToldOfIsTheSameStatement() {
        Proposition stated = Proposition.any(List.of(below(GATE, ValueIdentity.AT_THE_POSITION),
                truth(TermPath.of("x").then("open"), ValueIdentity.AT_THE_POSITION)));
        assertSame(stated, readThrough(stated, named(A)));
        Proposition told = Proposition.all(List.of(below(N, of(A)),
                below(GATE, ValueIdentity.AT_THE_POSITION)));
        assertSame(told, readThrough(told, named(B)), "a part told already keeps its name");
    }

    /**
     * Inside a quantifier over the items, what stands at the item is the quantifier's element,
     * whatever name it was told; what stands at an element of another container keeps its name.
     */
    @Test
    void whatStandsAtAQuantifiersElementIsTheQuantifiers() {
        TermPath other = TermPath.of("x").then("groups").element().then("m");
        Proposition element = Proposition.all(List.of(below(N, of(A)), below(other, of(B))));
        assertEquals(Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                        below(other, of(B)))),
                ReadThroughNames.ownedBy(new DecisionSubject.AnInput(ITEMS), element));
    }

    /**
     * A site's statement told the names of another copy of the site: the copy's one name for the
     * element, and the name it was told where the copy reads the element through two.
     */
    @Test
    void aStatementIsToldAgainThroughTheNamesOfAnotherCopy() {
        BindingId copy = new BindingId(new BindingOwner.OfValue("probe", "g"), 1);
        Proposition stated = Proposition.all(List.of(below(N, of(A)),
                below(GATE, ValueIdentity.AT_THE_POSITION)));
        assertEquals(Proposition.all(List.of(below(N, of(copy)),
                        below(GATE, ValueIdentity.AT_THE_POSITION))),
                ReadThroughNames.toldAgain(stated, named(copy)));
        assertSame(stated, ReadThroughNames.toldAgain(stated, named(copy, B)));
    }

    /** Said at positions alone, and read back for which elements it was told. */
    @Test
    void whatWasToldIsReadBackAndTakenOff() {
        Proposition told = Proposition.all(List.of(below(N, of(A)), truth(PAID, of(A))));
        assertEquals(named(A), ReadThroughNames.namedIn(told));
        assertEquals(Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                        truth(PAID, ValueIdentity.AT_THE_POSITION))),
                ReadThroughNames.atThePositions(told));
    }

    /** Which value at a position: the row's where no name stood for its element, the one name's
     *  where one did, and none where two did. */
    @Test
    void theValueAtAPositionIsTheOneNameThatStoodForItsElement() {
        assertEquals(ValueIdentity.AT_THE_POSITION, ReadThroughNames.identityAt(GATE, named(A)));
        assertEquals(of(A), ReadThroughNames.identityAt(N, named(A)));
        assertNull(ReadThroughNames.identityAt(N, named(A, B)));
    }
}
