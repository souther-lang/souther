package souther.compiler.check;

import souther.compiler.semantics.ArgumentRef;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementLineage.OutputLineage;
import souther.compiler.check.ElementLineage.ResultPath;
import souther.compiler.check.ElementLineage.Source;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The operations the declared table has no room for, said in this vocabulary.
 *
 * <p>None of them is declared and none of them needs to be for this to be worth holding. What is
 * being checked is the vessel: an operation the library already has, that {@link DischargeRules}
 * cannot state a rule about, has to be sayable here without a case of its own — or the abstraction
 * is the old one under a new name and the next combinator breaks it again.
 *
 * <p>They were found by asking what {@code Combinators} derives from a signature and what
 * {@link DischargeRules} declares beside it. Three things came back that neither could state: an
 * element that came from inside what a closure answered ({@code flatMap}), an answer holding more
 * than one run of elements ({@code partition}, {@code zipShortest}), and an element that came from
 * one of several arguments ({@code append}, {@code concat}).
 */
class WhereAnAnswersElementsCameFromCanBeSaidTest {

    private static final ArgumentRef FIRST = new ArgumentRef.At(0);

    private static final ArgumentRef SECOND = new ArgumentRef.At(1);

    private static final ArgumentRef CONTAINER = new ArgumentRef.TheContainer();

    private static ResultPath elementThen(ResultPath.Step step) {
        return ResultPath.elements().then(step);
    }

    /** {@code flatMap}: the element is inside what the closure answered of an input element. */
    @Test
    void anElementFromInsideWhatAClosureAnswered() {
        OutputLineage said = new OutputLineage(ResultPath.elements(),
                new ElementLineage.InsideClosureResult(new Source(CONTAINER, 1)));

        assertEquals("result[*]", said.at().toString());
        assertEquals(CONTAINER, said.origin().source().argument());
    }

    /**
     * {@code concat}: the element is an element of an element of the argument.
     *
     * <p>No case of its own. What a container of containers holds is two steps inside the argument,
     * which is what a source counts — so the lineage is the one a {@code filter} has, at a depth.
     */
    @Test
    void anElementFromTwoStepsInsideAnArgument() {
        OutputLineage said = new OutputLineage(ResultPath.elements(),
                new ElementLineage.SameAs(new Source(FIRST, 2)));

        assertEquals(2, said.origin().source().elements());
    }

    /** {@code partition}: two runs of elements, each the input's own. */
    @Test
    void anAnswerHoldingTwoRunsOfElements() {
        List<OutputLineage> said = List.of(
                new OutputLineage(new ResultPath(List.of(new ResultPath.Step.Component(0),
                                new ResultPath.Step.Element())),
                        new ElementLineage.SameAs(new Source(CONTAINER, 1))),
                new OutputLineage(new ResultPath(List.of(new ResultPath.Step.Component(1),
                                new ResultPath.Step.Element())),
                        new ElementLineage.SameAs(new Source(CONTAINER, 1))));

        assertEquals(List.of("result.0[*]", "result.1[*]"),
                said.stream().map(each -> each.at().toString()).toList());
    }

    /**
     * {@code zipShortest}: one run of elements, whose halves came from different arguments.
     *
     * <p>The other way round from {@code partition} — the element step comes first and the
     * components are inside it — which is why the place is a path and not a count of runs.
     */
    @Test
    void anAnswerWhosePartsCameFromDifferentArguments() {
        List<OutputLineage> said = List.of(
                new OutputLineage(elementThen(new ResultPath.Step.Component(0)),
                        new ElementLineage.SameAs(new Source(FIRST, 1))),
                new OutputLineage(elementThen(new ResultPath.Step.Component(1)),
                        new ElementLineage.SameAs(new Source(SECOND, 1))));

        assertEquals(List.of("result[*].0", "result[*].1"),
                said.stream().map(each -> each.at().toString()).toList());
        assertEquals(List.of(FIRST, SECOND),
                said.stream().map(each -> each.origin().source().argument()).toList());
    }

    /** {@code append}: the element came from one of two arguments, and nothing says which. */
    @Test
    void anElementFromOneOfSeveralArguments() {
        ElementLineage said = new ElementLineage.OneOf(List.of(
                new ElementLineage.SameAs(new Source(FIRST, 1)),
                new ElementLineage.SameAs(new Source(SECOND, 1))));

        assertEquals(null, said.source(),
                "which argument is not settled, so there is no one argument to answer with");
    }

    /**
     * And no shape is read off elements that came from more than one place.
     *
     * <p>Not an impossible state. {@code OneOf} is a lineage like the others and says something true
     * of {@code List.append}; what it is outside is the domain of the projection to
     * {@link DischargeRules.Shape}, whose four words are each about one source. So this is the
     * projection declining an input it has no word for, and the day {@code append} is declared the
     * thing to change is what the projection answers with — not the lineage, and not the table.
     *
     * <p>Answered rather than declined, {@code List.append(a, b)} would come under a rule saying its
     * elements are {@code a}'s, which its own declaration denies.
     */
    @Test
    void andNoShapeIsReadOffElementsFromMoreThanOnePlace() {
        DischargeRules.Built built = new DischargeRules.Built(
                new ElementLineage.OneOf(List.of(
                        new ElementLineage.SameAs(new Source(FIRST, 1)),
                        new ElementLineage.SameAs(new Source(SECOND, 1)))),
                DischargeRules.Cardinality.AT_MOST);

        assertThrows(IllegalStateException.class, built::shape);
    }
    /**
     * An element that is one of several things that happened to it, all at one place.
     *
     * <p>{@code Map.updateIfPresent} answers the map it was given with the value under one key
     * replaced. Every value in the answer came from that argument, and each is either the value that
     * was there or what the closure made of it — so what is unsettled is what happened, not where it
     * came from, and a reader asking where is owed the argument.
     */
    @Test
    void anElementThatIsOneOfSeveralThingsAtOnePlace() {
        ElementLineage said = new ElementLineage.OneOf(List.of(
                new ElementLineage.SameAs(new Source(CONTAINER, 1)),
                new ElementLineage.ClosureResult(new Source(CONTAINER, 1))));

        assertEquals(new Source(CONTAINER, 1), said.source(),
                "they came from one place, whatever happened to them there");
    }

    /**
     * And the word the four-word projection reads of it is the one that licenses nothing.
     *
     * <p>Neither {@code PERMUTES} nor {@code MAPS} is true of a run holding some of each: a reader
     * of the four words that took the first would assume of every value what is true of the ones the
     * closure never saw, and one that took the second would assume of them what is true of the one
     * it did. So the projection answers with the word for elements nothing was kept of, and a reader
     * that wants more asks the lineage, which says both.
     */
    @Test
    void aRunHoldingSomeOfEachIsProjectedToTheWordThatLicensesNothing() {
        DischargeRules.Built updated = new DischargeRules.Built(
                new ElementLineage.OneOf(List.of(
                        new ElementLineage.SameAs(new Source(CONTAINER, 1)),
                        new ElementLineage.ClosureResult(new Source(CONTAINER, 1)))),
                DischargeRules.Cardinality.SAME);

        assertEquals(DischargeRules.Shape.COLLAPSES, updated.shape());
    }

    /**
     * And the shape is coarser than what it is read off, which is why it is read off and not
     * declared.
     *
     * <p>{@code List.filterMap} and {@code Set.map} are one shape and two lineages. For the question
     * a shape answers they are the same — neither keeps what was stated of the source and neither
     * grows — and their elements come from different places: one is what the closure answered, and
     * the other is inside what the closure answered. Declared as shapes, that difference is not
     * written down anywhere and no later reader can recover it.
     */
    @Test
    void aShapeIsCoarserThanTheLineageItIsReadOff() {
        DischargeRules.Built collapsingMap = new DischargeRules.Built(
                new ElementLineage.ClosureResult(new Source(CONTAINER, 1)),
                DischargeRules.Cardinality.AT_MOST);
        DischargeRules.Built collapsingInside = new DischargeRules.Built(
                new ElementLineage.InsideClosureResult(new Source(CONTAINER, 1)),
                DischargeRules.Cardinality.AT_MOST);

        assertEquals(collapsingMap.shape(), collapsingInside.shape(),
                "one word for the two, which is what the discharge question needs");
        assertNotEquals(collapsingMap.lineage(), collapsingInside.lineage(),
                "and two answers to where the elements came from");
    }
}