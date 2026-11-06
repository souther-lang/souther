package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Which conditions on a way are taken in as statements of one value ({@link ElementsOnTheWay}),
 * asked of ways written out here: truths at an element of {@code x.items}, each read through a
 * name for the element, and a truth of the row, {@code x.open}.
 */
class AWayHoldsOneElementOfAContainerTest {

    private static final TermPath ITEMS = TermPath.of("x").then("items");
    private static final TermPath PAID = ITEMS.element().then("paid");
    private static final TermPath OPEN = TermPath.of("x").then("open");

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static final ElementsNamed.Slot AN_ITEM = new ElementsNamed.Slot(
            new InputReads.ContainerOf.AtAPosition(ITEMS), HeldIn.Part.ELEMENT);

    private static final List<WhyNotTaken> ANOTHER_ELEMENT = List.of(new WhyNotTaken.OutsideDomain(
            WhyNotTaken.DomainLimit.ANOTHER_ELEMENT_THAN_THE_WAY_HOLDS));

    private static ConditionOccurrence condition(int ordinal) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, ordinal);
    }

    private static ConditionReportAnchor anchor(int ordinal) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("probe", condition(ordinal));
    }

    private static ElementsNamed named(BindingId... names) {
        return ElementsNamed.of(List.of(names).stream()
                .map(name -> new ElementsNamed.Named(AN_ITEM, name)).toList());
    }

    /** The truth at {@code at}, the condition numbered {@code ordinal}, read through {@code names}. */
    private static OnTheWay truth(int ordinal, TermPath at, BindingId... names) {
        return new OnTheWay.TakenIn(anchor(ordinal), new RowDemand.ATruth(at, true),
                NamedElements.of(condition(ordinal), named(names)));
    }

    private static OnTheWay declined(int ordinal) {
        return new OnTheWay.Declined(condition(ordinal), anchor(ordinal), ANOTHER_ELEMENT,
                Optional.empty(), Optional.empty());
    }

    /** A way no name stood for an element on is the way it was. */
    @Test
    void aWayOfTheRowIsTheWayItWas() {
        List<OnTheWay> way = List.of(truth(0, OPEN), truth(1, PAID));
        assertSame(way, ElementsOnTheWay.keptToOneElementEach(way, ElementsNamed.NONE));
    }

    /** The first name the way met the element by is kept, what was read through another is
     *  declined, and the row's condition stays. */
    @Test
    void theFirstNameMetIsKept() {
        assertEquals(List.of(truth(0, PAID, A), declined(1), truth(2, OPEN), truth(3, PAID, A)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A),
                        truth(1, PAID, B), truth(2, OPEN), truth(3, PAID, A)), ElementsNamed.NONE));
    }

    /** Where the border reads the element, the name it reads it through is kept. */
    @Test
    void theNameTheBorderReadsIsKept() {
        assertEquals(List.of(declined(0), truth(1, PAID, B)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A),
                        truth(1, PAID, B)), named(B)));
    }

    /** Where the border reads the element through two names, nothing on the way is kept for it;
     *  a condition read through two names is declined whatever is kept. */
    @Test
    void twoNamesAtOnceAreNoOneElement() {
        assertEquals(List.of(declined(0), truth(1, OPEN)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A),
                        truth(1, OPEN)), named(A, B)));
        assertEquals(List.of(truth(0, PAID, A), declined(1)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A),
                        truth(1, PAID, A, B)), ElementsNamed.NONE));
    }

    /** A condition of several ways is declined whole where one of its ways reads another
     *  element: what it states is one statement of all of them. */
    @Test
    void aConditionOfSeveralWaysIsDeclinedWhole() {
        OnTheWay several = OnTheWay.OneOf.of(condition(1), anchor(1),
                List.of(List.of(truth(1, PAID, B)), List.of(truth(1, OPEN))), Optional.empty());
        assertEquals(List.of(truth(0, PAID, A), declined(1)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A), several),
                        ElementsNamed.NONE));
    }
}
