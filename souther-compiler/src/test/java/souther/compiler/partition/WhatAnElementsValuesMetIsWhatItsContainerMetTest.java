package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What stopped the values offered for an element is what stopped the container built of them.
 *
 * <p>A value of {@code Huge} holds more elements than a proposal holds, so none is built, and a
 * set of two of them is built of values that are not there. Said of the set alone, that reads as a
 * set nothing can build; what it is, is a set this compiler declined to build, and the figure it
 * declined at is what the values of the element met.
 *
 * <p>Two other ways of being short are kept apart from it. A type with too few values — a set of
 * three booleans — met nothing, because nothing was declined; and a build that found every value
 * it was asked for met nothing either, whatever one of its steps was stopped by on the way.
 */
class WhatAnElementsValuesMetIsWhatItsContainerMetTest {

    private static final String MODULE = """
            module p

            data Huge = List<Bool>
              invariant List.length(value) >= 65
            data Near = List<Bool>
              invariant List.length(value) >= 64
            data Long = String
              invariant String.length(value) >= 4097

            data Held = { h: Huge, n: Int }
            data Both = { h: Huge, s: Long }

            data Small = { n: Int }
            data Large = { h: Huge }
            data Either = Small | Large
            """;

    private static final RuleReadingSource RULES = RuleReadings.ofSource(MODULE);

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES);

    private static final Set<CompositionBudget> ELEMENTS =
            Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS);

    private static Type named(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey(RULES.symbols().module(), name)));
    }

    private static TypeView position(Type type) {
        return TypeView.asWritten(type, RULES.symbols(), RULES.kinds(), RULES.sums());
    }

    private static Proposals ofSize(Type type, int size) {
        return Witnesses.ofSize(position(type), size, List.of(), READING, Set.of());
    }

    /** A set of two of a value no proposal holds is built of nothing, and says which figure. */
    @Test
    void aSetOfValuesPastTheFigureSaysTheFigure() {
        Proposals made = ofSize(new Type.SetOf(named("Huge")), 2);

        assertEquals(List.of(), made.values());
        assertEquals(ELEMENTS, made.met().figures());
    }

    /** One element short of the figure is built, and met nothing. */
    @Test
    void aSetOfValuesAtTheFigureIsBuilt() {
        Proposals made = ofSize(new Type.SetOf(named("Near")), 2);

        assertFalse(made.values().isEmpty(), "two lists of sixty-four are two values");
        assertTrue(made.met().nothing(), () -> made.met().toString());
    }

    /** A type with too few values is the model's answer, and nothing of this compiler's. */
    @Test
    void aSetTheTypeHasTooFewValuesForMetNothing() {
        Proposals made = ofSize(new Type.SetOf(Type.BOOL), 3);

        assertEquals(List.of(), made.values());
        assertTrue(made.met().nothing(), () -> made.met().toString());
    }

    /**
     * A list of two is built of what the element is offered, which is a value its rules refuse —
     * and says what kept the value they ask for from being among them.
     */
    @Test
    void aListOfValuesPastTheFigureCarriesTheFigureBesideWhatWasBuilt() {
        assertEquals(ELEMENTS, ofSize(new Type.ListOf(named("Huge")), 2).met().figures());
    }

    /** The same of a map's values. */
    @Test
    void aMapOfValuesPastTheFigureSaysTheFigure() {
        assertEquals(ELEMENTS,
                ofSize(new Type.MapOf(Type.STRING, named("Huge")), 2).met().figures());
    }

    /** And of a record holding one: what its field met is what the record met. */
    @Test
    void aSetOfRecordsHoldingAValuePastTheFigureSaysTheFigure() {
        Proposals made = ofSize(new Type.SetOf(named("Held")), 2);

        assertEquals(ELEMENTS, made.met().figures(), () -> made.values().toString());
    }

    /** Two fields past two figures are both said, and neither stands for the other. */
    @Test
    void twoFiguresMetByTwoFieldsAreBothSaid() {
        Proposals made = ofSize(new Type.SetOf(named("Both")), 2);

        assertEquals(Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS,
                CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS), made.met().figures());
    }

    /**
     * A walk that found what it was asked for says nothing of a figure one of its steps met.
     *
     * <p>A sum's values are its cases' values, and one case of this one is past the figure while
     * the other has as many as anybody asks. Carried on, the figure would stand under a refusal of
     * values the walk had plenty of.
     */
    @Test
    void valuesFoundInFullSayNothingOfAFigureOnTheWay() {
        Proposals found = Witnesses.distinctValuesOf(named("Either"), 3, READING, Set.of());

        assertEquals(3, found.values().size(), () -> found.values().toString());
        assertTrue(found.met().nothing(), () -> found.met().toString());
    }

    /**
     * A container its rules leave no room in met nothing; one past what a proposal holds met the
     * figure. Both build nothing, and only what they met tells a reader which to act on.
     */
    @Test
    void noRoomIsTheModelsAndPastTheFigureIsThisCompilers() {
        Shape.Sequence list = new Shape.Sequence(Shape.Sequence.Kind.LIST, Type.BOOL);
        Proposals noRoom = Witnesses.holding(list, List.of(), List.of(), List.of(),
                new DeclaredBounds.CountRange(3, 2), READING);
        Proposals pastTheFigure = Witnesses.holding(list, List.of(), List.of(), List.of(),
                new DeclaredBounds.CountRange(
                        CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS.maximum() + 1,
                        Integer.MAX_VALUE), READING);

        assertEquals(List.of(), noRoom.values());
        assertTrue(noRoom.met().nothing(), () -> noRoom.met().toString());
        assertEquals(List.of(), pastTheFigure.values());
        assertEquals(ELEMENTS, pastTheFigure.met().figures());
    }

    /** What a position is offered says what kept the value its rules ask for out of the offer. */
    @Test
    void whatAPositionIsOfferedSaysTheFigureItsRulesAreBeyond() {
        Proposals offered = Partitions.representativesOf(named("Huge"), READING);

        assertEquals(ELEMENTS, offered.met().figures(), () -> offered.values().toString());
    }
}
