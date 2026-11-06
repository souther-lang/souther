package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The way to a line, once the case where the line decides is on it, holds only what is read of the
 * elements the comparison reads.
 *
 * <p>A case names the elements of the conditions it is made of, and those can be another name for
 * an element of the same container: {@code a.n < 0} is on the way to the line of {@code b.n >= 1}
 * in {@code a.n < 0 && b.n >= 1}. A line is looked for as a statement of its own element, so a
 * condition read of the other name stays on the way declined; held as it was, it is composed with
 * a point of the line's element as though both were asked of one.
 */
class TheWayToALineIsKeptToTheElementsTheLineReadsTest {

    private static final TermPath ITEMS = TermPath.of("x").then("items");
    private static final TermPath PAID = ITEMS.element().then("paid");

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final BindingId A = new BindingId(OWNER, 1);
    private static final BindingId B = new BindingId(OWNER, 2);

    private static final ElementsNamed.Slot AN_ITEM = new ElementsNamed.Slot(
            new InputReads.ContainerOf.AtAPosition(ITEMS), HeldIn.Part.ELEMENT);

    private static ConditionOccurrence condition(int ordinal) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, ordinal);
    }

    private static ConditionReportAnchor anchor(int ordinal) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("probe", condition(ordinal));
    }

    private static ElementsNamed reads(BindingId name) {
        return ElementsNamed.of(List.of(new ElementsNamed.Named(AN_ITEM, name)));
    }

    /** The truth at an element of {@code x.items}, read through {@code name}. */
    private static OnTheWay truth(int ordinal, BindingId name) {
        return new OnTheWay.TakenIn(anchor(ordinal), new RowDemand.ATruth(PAID, true),
                NamedElements.of(condition(ordinal), reads(name)));
    }

    private static OnTheWay declined(int ordinal) {
        return new OnTheWay.Declined(condition(ordinal), anchor(ordinal),
                ElementsOnTheWay.ANOTHER_ELEMENT, Optional.empty(), Optional.empty());
    }

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("probe", "f"), ordinal, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL);
    }

    private static WhereAPartDecides aCase() {
        return new WhereAPartDecides(new PlaceOfALine(PartOfAComparison.of(
                WrittenLine.THE_COMPARISON), Spelling.of("line")), new Proposition.Truth(
                new DecisionSubject.AnInput(TermPath.of("paid")), true));
    }

    /**
     * The way filed to the line {@code states} draws where {@code decides}, when the comparison
     * reads {@code readsTheElements} and the case put {@code put} on the way.
     */
    private static List<OnTheWay> wayToTheLine(ElementsNamed readsTheElements, List<OnTheWay> put) {
        return madeFor(readsTheElements, put).byLine().get(lineOfTheCase());
    }

    private static ReachingCuts.ALine lineOfTheCase() {
        return new ReachingCuts.ALine(copy(0), Optional.of(aCase()));
    }

    private static ReachingCuts madeFor(ElementsNamed readsTheElements, List<OnTheWay> put) {
        Map<WhereAPartDecides, ReachingCuts.Stating> cases = new LinkedHashMap<>();
        cases.put(aCase(), ReachingCuts.Stating.of(put, ModelOccurrences.of(copy(1))));
        ReachingCuts.Collected collected = new ReachingCuts.Collected();
        collected.reached(copy(0), List.of(), readsTheElements, cases,
                ReachingCuts.Stating.of(List.of(), ModelOccurrences.of(copy(1))).by());
        return collected.made();
    }

    /** A condition declined for another name is told of the copy that put the condition it was
     *  made of, so that a gap naming it says where it came from. */
    @Test
    void aDeclinedConditionIsToldWhatPutTheOneItWasMadeOf() {
        ReachingCuts made = madeFor(reads(B), List.of(truth(0, A), truth(1, B)));
        assertEquals(ModelOccurrences.of(copy(1)), made.saidByLine().get(lineOfTheCase())
                .of(new ConditionGap.OfTheInput(new ReachabilityGap.Unstated(
                        (OnTheWay.Declined) declined(0)))));
    }

    /** What the case read of another name for the element is declined, whichever name was met
     *  first. */
    @Test
    void aConditionOnAnotherNameIsDeclined() {
        assertEquals(List.of(declined(0), truth(1, B)),
                wayToTheLine(reads(B), List.of(truth(0, A), truth(1, B))));
        assertEquals(List.of(truth(0, A), declined(1)),
                wayToTheLine(reads(A), List.of(truth(0, A), truth(1, B))));
    }

    /** A line that reads no element names none to keep, so the first name met is kept. */
    @Test
    void aLineThatReadsNoElementKeepsTheFirstNameMet() {
        assertEquals(List.of(truth(0, A), declined(1)),
                wayToTheLine(ElementsNamed.NONE, List.of(truth(0, A), truth(1, B))));
    }
}
