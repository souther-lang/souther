package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

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

    /** Where the border reads the element through a name and through one not known, no name is
     *  the one it reads it through: nothing on the way is kept for the element. */
    @Test
    void anElementAlsoReadThroughAnUnknownNameIsKeptForNoName() {
        ElementsNamed border = ElementsNamed.of(
                List.of(new ElementsNamed.Named(AN_ITEM, B)), Set.of(AN_ITEM));
        assertEquals(List.of(declined(0), declined(1)),
                ElementsOnTheWay.keptToOneElementEach(List.of(truth(0, PAID, A),
                        truth(1, PAID, B)), border));
    }

    /** A way is made of conditions that already hold one name for each element: the first name
     *  met is chosen where only arrival is asked, and not where a way is made. */
    @Test
    void aWayIsNotMadeByChoosingAName() {
        List<OnTheWay> two = List.of(truth(0, PAID, A), truth(1, PAID, B));
        assertThrows(IllegalArgumentException.class, () -> new WayToTheBorder(two));
        assertEquals(List.of(truth(0, PAID, A), declined(1)),
                WayToTheBorder.forArrival(two).onTheWay());
    }

    /** What put a condition on the way is told of the condition declined in its place, where a
     *  gap names it. */
    @Test
    void aDeclinedConditionIsToldWhatPutTheOneItWasMadeOf() {
        OnTheWay put = truth(0, PAID, A);
        ModelOccurrence copy = new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("probe", "f"), 7, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL);
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(put, ModelOccurrences.of(copy));

        ElementsOnTheWay.Kept kept = ElementsOnTheWay.keptToOneElementEach(List.of(put),
                named(B), filing.said());

        assertEquals(List.of(declined(0)), kept.way());
        assertEquals(ModelOccurrences.of(copy), kept.said().of(new ConditionGap.OfTheInput(
                new ReachabilityGap.Unstated((OnTheWay.Declined) kept.way().getFirst()))));
    }

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("probe", "f"), ordinal, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL);
    }

    private static ConditionGap gapOf(OnTheWay declined) {
        return new ConditionGap.OfTheInput(
                new ReachabilityGap.Unstated((OnTheWay.Declined) declined));
    }

    /** Two conditions of one condition occurrence declined for one reason are one declined
     *  condition, told of what put either. */
    @Test
    void conditionsDeclinedAsOneAreToldWhatPutEither() {
        TermPath tier = ITEMS.element().then("tier");
        OnTheWay paid = new OnTheWay.TakenIn(anchor(0), new RowDemand.ATruth(PAID, true),
                NamedElements.of(condition(0), named(A)));
        OnTheWay ofTier = new OnTheWay.TakenIn(anchor(0), new RowDemand.ATruth(tier, true),
                NamedElements.of(condition(0), named(A)));
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(paid, ModelOccurrences.of(copy(1)));
        filing.alone(ofTier, ModelOccurrences.of(copy(2)));

        ElementsOnTheWay.Kept kept = ElementsOnTheWay.keptToOneElementEach(
                List.of(paid, ofTier), named(B), filing.said());

        assertEquals(ModelOccurrences.of(List.of(copy(1), copy(2))),
                kept.said().of(gapOf(kept.way().getFirst())));
    }

    /** A way kept for arrival has no account of its own, and a gap naming a condition it declined
     *  is told of what put the conditions of that place. */
    @Test
    void aConditionDeclinedForArrivalIsToldWhatPutTheConditionsOfItsPlace() {
        OnTheWay put = truth(0, PAID, A);
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(put, ModelOccurrences.of(copy(1)));
        List<OnTheWay> way = WayToTheBorder.forArrival(List.of(truth(1, PAID, B), put))
                .onTheWay();

        assertEquals(ModelOccurrences.of(copy(1)), filing.said().of(gapOf(declined(0))));
        assertEquals(List.of(truth(1, PAID, B), declined(0)), way);
    }

    /** Who put what is told in the order of the way, which a declined condition does not move. */
    @Test
    void whoPutWhatIsToldInTheOrderOfTheWay() {
        OnTheWay first = truth(0, PAID, A);
        OnTheWay second = truth(1, PAID, B);
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(first, ModelOccurrences.of(copy(1)));
        filing.alone(second, ModelOccurrences.of(copy(2)));

        ElementsOnTheWay.Kept kept = ElementsOnTheWay.keptToOneElementEach(
                List.of(first, second), named(B), filing.said());

        assertEquals(kept.way(), List.copyOf(kept.said().entries().keySet()));
    }

    /** What stood inside a condition of several ways that is declined whole is no longer on the
     *  way, and is not told of. */
    @Test
    void whatWasInsideADeclinedConditionIsNotToldOf() {
        OnTheWay several = OnTheWay.OneOf.of(condition(1), anchor(1),
                List.of(List.of(truth(1, PAID, B)), List.of(truth(1, OPEN))), Optional.empty());
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.each(List.of(several), ModelOccurrences.of(copy(1)));

        ElementsOnTheWay.Kept kept = ElementsOnTheWay.keptToOneElementEach(
                List.of(truth(0, PAID, A), several), ElementsNamed.NONE, filing.said());

        assertEquals(List.of(kept.way().get(1)), List.copyOf(kept.said().entries().keySet()));
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
