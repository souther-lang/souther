package souther.compiler.meaning;

import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.StringContainment;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a statement is told of the names it was read through ({@link ReadThroughNames}), asked of
 * statements written out here: a number and a truth at an element of {@code x.items} and a number
 * of the row, {@code x.gate}, with {@code a} and {@code b} two names for elements of the items.
 */
class WhatANameStoodForIsTheValueAPartIsAboutTest {

    private static final TermPath ITEMS = TermPath.of("x").then("items");
    private static final TermPath N = ITEMS.element().then("n");
    private static final TermPath PAID = ITEMS.element().then("paid");
    private static final TermPath TEXT = ITEMS.element().then("text");
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
     * Inside a quantifier over the items handed {@code a} from outside, what stands at the item
     * untold, or told {@code b}, a name it was not handed and so its own closure's, is the
     * quantifier's element; a part there told {@code a} is another element, which is a part
     * nothing read; what stands at an element of another container keeps its name.
     */
    @Test
    void aQuantifiersElementIsItsOwnAndANameItWasHandedIsAnotherElement() {
        TermPath other = TermPath.of("x").then("groups").element().then("m");
        Proposition element = Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                truth(PAID, of(B)), below(N.then("m"), of(A)), below(other, of(B))));
        assertEquals(Proposition.all(List.of(below(N, ValueIdentity.AT_THE_POSITION),
                        truth(PAID, ValueIdentity.AT_THE_POSITION), TWO_AS_ONE,
                        below(other, of(B)))),
                ReadThroughNames.ownedBy(new DecisionSubject.AnInput(ITEMS), A::equals, element,
                        () -> TWO_AS_ONE));
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

    /**
     * A value inside an element of a container another element holds is told the name of the
     * inner element and no other: where none stood for it, it is the element of whatever goes over
     * it, and the outer element's name, which says only which outer element it is in, is not told.
     */
    @Test
    void aValueIsToldTheNameOfItsInnermostElementOnly() {
        TermPath inner = ITEMS.element().then("subs").element().then("m");
        Proposition stated = below(inner, ValueIdentity.AT_THE_POSITION);
        assertSame(stated, readThrough(stated, named(A)));
    }

    /** A string at an element's position is a subject as any other: told the name, and a part
     *  nothing read where two names stood for the element. */
    @Test
    void aStringAtAnElementIsToldItsName() {
        StringsLanguage starts = new StringsLanguage(PatternMeaning.text("X"));
        Proposition stated = new Proposition.InTheStrings(
                new Proposition.InTheStrings.Strings.AtAPosition(TEXT), starts, true);
        assertEquals(new Proposition.InTheStrings(
                        new Proposition.InTheStrings.Strings.AtAPosition(TEXT, of(A)), starts, true),
                readThrough(stated, named(A)));
        assertSame(TWO_AS_ONE, readThrough(stated, named(A, B)));
    }

    /** How many of some statements hold is told what each statement is told. */
    @Test
    void aCountOfStatementsIsToldWhatItsStatementsAre() {
        Proposition stated = Proposition.SoManyHold.counting(List.of(
                below(N, ValueIdentity.AT_THE_POSITION), below(GATE, ValueIdentity.AT_THE_POSITION)),
                List.of(1, 1), List.of(1));
        assertEquals(Proposition.SoManyHold.counting(List.of(below(N, of(A)),
                        below(GATE, ValueIdentity.AT_THE_POSITION)), List.of(1, 1), List.of(1)),
                readThrough(stated, named(A)));
    }

    /**
     * A count of the elements of a container inside an element is told which element's container
     * it counts, and what it asks of each element it counts is of its own element.
     */
    @Test
    void aCountIsToldWhoseContainerItCounts() {
        TermPath subs = ITEMS.element().then("subs");
        DecisionSubject.AnInput counted = new DecisionSubject.AnInput(subs);
        Proposition each = below(subs.element().then("m"), ValueIdentity.AT_THE_POSITION);
        Proposition stated = Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                new Quantity.HowManyMeet(counted, each), ExactRatio.ONE), Rel.GE), true);
        assertEquals(Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                        new Quantity.HowManyMeet(new DecisionSubject.AnInput(subs, of(A)), each),
                        ExactRatio.ONE), Rel.GE), true),
                readThrough(stated, named(A)));
    }

    private static Quantity uppercased(ValueIdentity identity) {
        return new Quantity.WhatAnOperationAnswers(ValueName.Stdlib.operation("String",
                "uppercase"), List.of(number(TEXT, identity)));
    }

    /** A string an operation made of an element's string is told the element's name inside it,
     *  so two elements' made strings are two values, however deep the making. */
    @Test
    void aStringMadeOfAnElementsStringIsToldItsName() {
        Proposition stated = new Proposition.StringInside(uppercased(ValueIdentity.AT_THE_POSITION),
                number(GATE, ValueIdentity.AT_THE_POSITION), StringContainment.ANYWHERE, true);
        assertEquals(new Proposition.StringInside(uppercased(of(A)),
                        number(GATE, ValueIdentity.AT_THE_POSITION), StringContainment.ANYWHERE,
                        true),
                readThrough(stated, named(A)));
    }

    /** A product of two numbers is told which value each factor is, whichever order the factors
     *  are held in. */
    @Test
    void aProductIsToldWhichValueEachFactorIs() {
        NumericTerm.ValueOf n = new NumericTerm.ValueOf(N);
        NumericTerm.ValueOf gate = new NumericTerm.ValueOf(GATE);
        Proposition stated = Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                new Quantity.ProductOfTwo(n, gate), ExactRatio.ZERO), Rel.GE), true);
        assertEquals(Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                        new Quantity.ProductOfTwo(gate, ValueIdentity.AT_THE_POSITION, n, of(A)),
                        ExactRatio.ZERO), Rel.GE), true),
                readThrough(stated, named(A)));
    }

    /**
     * A number read off places in two elements — the product of an item's number by a group's —
     * holds which value it is about at the place it is filed under only: told the other element
     * as well, it is no one number, and told none there, it is the one at its own.
     */
    @Test
    void aNumberOfTwoElementsHoldsWhichValueAtOneOfThemOnly() {
        TermPath ofAGroup = TermPath.of("x").then("groups").element().then("m");
        NumericTerm.ProductOf product = NumericTerm.ProductOf.signed(
                LinearForm.atom(new NumericTerm.ValueOf(N)),
                LinearForm.atom(new NumericTerm.ValueOf(ofAGroup))).product();
        Proposition stated = Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                new DecisionAtom.OfTheInput(product), ExactRatio.ZERO), Rel.GE), false);
        ElementsNamed both = ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, A),
                new ElementsNamed.Named(ElementsNamed.Slot.innermostOf(ofAGroup), B)));
        assertSame(TWO_AS_ONE, readThrough(stated, both));
        ElementsNamed itsOwn = product.subjectPath().equals(N) ? named(A)
                : ElementsNamed.of(List.of(new ElementsNamed.Named(
                        ElementsNamed.Slot.innermostOf(ofAGroup), B)));
        assertInstanceOf(Proposition.Compared.class, readThrough(stated, itsOwn));
    }

    /** A number that holds a position and no place to say which value there it is about is no
     *  one number where a name was told that position: a part nothing read. */
    @Test
    void aNumberWithNoPlaceForWhichValueIsNoOneNumberWhereANameWasTold() {
        Proposition stated = Proposition.compared(new Relation.Affine(LinearForm.atomMinusConstant(
                new Quantity.HowManyDifferentBelow(ITEMS.element().then("tree"), List.of("next"),
                        GATE, List.of(), List.of()), ExactRatio.ZERO), Rel.GE), true);
        assertSame(TWO_AS_ONE, readThrough(stated, named(A)));
        assertSame(stated, readThrough(stated, ElementsNamed.NONE));
    }

    /** One value at each element's position: the first met is kept and a part reading another
     *  there is a part nothing read, the rest as it stood. */
    @Test
    void aStatementHandedOnHoldsOneValueAtEachElement() {
        Proposition stated = Proposition.all(List.of(truth(PAID, of(A)), truth(PAID, of(B)),
                below(GATE, ValueIdentity.AT_THE_POSITION)));
        Proposition kept = ReadThroughNames.oneValueAtEachElement(stated, () -> TWO_AS_ONE);
        assertEquals(Proposition.all(List.of(truth(PAID, of(A)), TWO_AS_ONE,
                below(GATE, ValueIdentity.AT_THE_POSITION))), kept);
        assertTrue(ReadThroughNames.holdsOneValueAtEachElement(kept));
        assertFalse(ReadThroughNames.holdsOneValueAtEachElement(stated));
    }

    /**
     * Two statements are one statement whatever they named their values only where the names
     * stand one to one: {@code a.paid && !a.paid} and {@code a.paid && !b.paid} are one statement
     * at positions and two in what they say.
     */
    @Test
    void twoStatementsAreOneOnlyWhereTheirNamesStandOneToOne() {
        Proposition oneValue = Proposition.all(List.of(truth(PAID, of(A)),
                truth(PAID, of(A)).denied()));
        Proposition twoValues = Proposition.all(List.of(truth(PAID, of(A)),
                truth(PAID, of(B)).denied()));
        BindingId c = new BindingId(OWNER, 3);
        BindingId d = new BindingId(OWNER, 4);
        Proposition twoRenamed = Proposition.all(List.of(truth(PAID, of(c)),
                truth(PAID, of(d)).denied()));
        assertFalse(ReadThroughNames.sameUpToTheNames(oneValue, twoValues));
        assertTrue(ReadThroughNames.sameUpToTheNames(twoValues, twoRenamed));
    }

    private static Proposition startsWith(String text, ValueIdentity identity) {
        return new Proposition.InTheStrings(new Proposition.InTheStrings.Strings.AtAPosition(TEXT,
                identity), new StringsLanguage(PatternMeaning.text(text)), true);
    }

    /**
     * Which statement a name stands in is what is compared, and not the order the names come in:
     * a statement puts its parts in an order its names have a part in, so one asking the first
     * value twice and another asking the second twice can list their names alike.
     */
    @Test
    void twoStatementsAreOneOnlyWhereEachPartIsToldTheNameTheOtherIs() {
        BindingId c = new BindingId(OWNER, 4);
        BindingId d = new BindingId(OWNER, 3);
        Proposition xAndYOfOne = Proposition.all(List.of(startsWith("X", of(A)),
                startsWith("Y", of(A)), startsWith("Z", of(B))));
        Proposition yAndZOfOne = Proposition.all(List.of(startsWith("X", of(c)),
                startsWith("Y", of(d)), startsWith("Z", of(d))));
        Proposition xAndYRenamed = Proposition.all(List.of(startsWith("X", of(d)),
                startsWith("Y", of(d)), startsWith("Z", of(c))));
        assertFalse(ReadThroughNames.sameUpToTheNames(xAndYOfOne, yAndZOfOne));
        assertFalse(ReadThroughNames.sameUpToTheNames(yAndZOfOne, xAndYOfOne));
        assertTrue(ReadThroughNames.sameUpToTheNames(xAndYOfOne, xAndYRenamed));
        assertTrue(ReadThroughNames.sameUpToTheNames(xAndYRenamed, xAndYOfOne));
    }

    /** Told again where the copy's name for one element is the name the site has for another,
     *  which the copy has no name for: the two stay two. */
    @Test
    void aNameIsNeverToldAgainOntoOneTheSiteKeeps() {
        TermPath ofAGroup = TermPath.of("x").then("groups").element().then("m");
        Proposition stated = Proposition.all(List.of(below(N, of(A)), below(ofAGroup, of(B))));
        assertSame(stated, ReadThroughNames.toldAgain(stated, named(B)));
    }

    /** Told again through a copy that has one name where the site had two, the site keeps its
     *  names: two values are never told one. */
    @Test
    void twoValuesAreNeverToldAgainAsOne() {
        TermPath other = TermPath.of("x").then("groups").element().then("m");
        ElementsNamed.Slot aGroup = new ElementsNamed.Slot(new InputReads.ContainerOf.AtAPosition(
                TermPath.of("x").then("groups")), HeldIn.Part.ELEMENT);
        BindingId copy = new BindingId(new BindingOwner.OfValue("probe", "g"), 1);
        Proposition stated = Proposition.all(List.of(below(N, of(A)), below(other, of(B))));
        ElementsNamed oneName = ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, copy),
                new ElementsNamed.Named(aGroup, copy)));
        assertSame(stated, ReadThroughNames.toldAgain(stated, oneName));
    }

    /** And where it had three: however many names of the site the copy's one name meets, none of
     *  them is told it. */
    @Test
    void threeValuesAreNeverToldAgainAsOne() {
        TermPath ofAGroup = TermPath.of("x").then("groups").element().then("m");
        TermPath ofATag = TermPath.of("x").then("tags").element().then("m");
        BindingId third = new BindingId(new BindingOwner.OfValue("probe", "c"), 1);
        BindingId copy = new BindingId(new BindingOwner.OfValue("probe", "g"), 1);
        Proposition stated = Proposition.all(List.of(below(N, of(A)), below(ofAGroup, of(B)),
                below(ofATag, of(third))));
        ElementsNamed oneName = ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, copy),
                new ElementsNamed.Named(ElementsNamed.Slot.innermostOf(ofAGroup), copy),
                new ElementsNamed.Named(ElementsNamed.Slot.innermostOf(ofATag), copy)));
        assertSame(stated, ReadThroughNames.toldAgain(stated, oneName));
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
