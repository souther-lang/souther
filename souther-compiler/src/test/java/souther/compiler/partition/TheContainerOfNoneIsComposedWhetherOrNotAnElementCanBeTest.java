package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The container of none is a container wherever the region leaves it, whether or not an element
 * can be: where the rules of an element leave it no number, a count of none is still met by it
 * and a count of one by no container at all — said as that, and not as a search stopped at the
 * totals it tried, since no total turns on an element there is none of.
 *
 * <p>And nowhere the region does not leave it. A rule holding what the elements come to to no
 * number holds the container of none to it as well, and a region that took in a condition about
 * an element handed on the way is one where the container holds that element.
 *
 * <p>The smallest case that asks it: a list of whole numbers, and how many of them are above half
 * of what they come to.
 */
class TheContainerOfNoneIsComposedWhetherOrNotAnElementCanBeTest {

    /** The numbers, with nothing said of them. */
    private static final String NUMBERS = """
            module g

            data Ok

            behavior counted : (xs: List<Int>) -> Ok
            """;

    /** Numbers no element can hold: every element's own rule leaves it none. */
    private static final String NO_NUMBER = """
            module g

            data P = { n: Int } invariant n > 10 && n < 0

            data Ok

            behavior counted : (xs: List<P>) -> Ok
            """;

    /** Numbers whose total the rule of the record holding them leaves no number. */
    private static final String NO_TOTAL = """
            module g

            data Box = { xs: List<Int> } invariant List.sum(xs) > 10 && List.sum(xs) < 0

            data Ok

            behavior counted : (b: Box) -> Ok
            """;

    /** An input read, and the count of its numbers above half of their sum. */
    private record Case(Quantities measuring, RuleReadingContext reading, TermPath xs,
                        Type list, NumericTerm.ValueOf number, RealizationTarget.ACount count,
                        SequencedMap<RealizationTarget, AskedAt> demands) {}

    /**
     * The count of {@code asked} of the numbers of the list at {@code path} in {@code source},
     * each at {@code field} inside an element where it is not null.
     */
    private static Case theCase(String source, String path, String field, long asked) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(path)).findFirst().orElseThrow();
        Quantities measuring = input.quantities(rules);
        TermPath at = field == null ? xs.element() : xs.element().then(field);
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(at);
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(at), Type.INT, rules.inners(),
                rules.symbols());
        // the total less twice the number is below nought, which is not at or above it: the
        // number is above half the total
        Proposition above = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.ZERO, Map.of(new DecisionAtom.OfTheInput(total), ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(number), ExactRatio.of(-2))), Rel.GE), false);
        RealizationTarget.ACount count = new RealizationTarget.ACount(CountedElements.of(
                "counted", new Quantity.HowManyMeet(new DecisionSubject.AnInput(xs), above),
                measuring, AnElementMeeting.UNREAD));
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        demands.put(count, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                new Level.OfTheQuantity(ExactRatio.of(asked)))), Count.of(asked)));
        return new Case(measuring, reading, xs, input.typeAt(xs, rules), number, count,
                demands);
    }

    private static Case ofNumbers(long asked) {
        return theCase(NUMBERS, "xs", null, asked);
    }

    private static Case ofNoNumber(long asked) {
        return theCase(NO_NUMBER, "xs", "n", asked);
    }

    private static TermRealizations.Realization composed(Case made, SearchRegion region) {
        return CardinalityComposer.compose(made.list(), List.of(), made.xs(),
                List.of(made.count()), List.of(), made.demands(), null, List.of(), List.of(),
                made.measuring(), region, made.reading());
    }

    /** Whether some container {@code built} offers holds no element. */
    private static boolean holdsTheContainerOfNone(TermRealizations.Realization built) {
        return built instanceof TermRealizations.Realization.Built made
                && made.values().stream().anyMatch(each -> each.text().contains("[]"));
    }

    @Test
    void whereNoNumberIsLeftTheContainerOfNoneMeetsACountOfNone() {
        Case made = ofNoNumber(0);
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                made.measuring().region().projectionOf(made.number()),
                "the control: the element's rule leaves it no number");
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class,
                composed(made, made.measuring().region()));
        assertEquals(1, built.values().size(), "the container of none, and no other");
        assertTrue(holdsTheContainerOfNone(built), built.values().toString());
    }

    @Test
    void whereNoNumberIsLeftNoContainerMeetsACountOfOne() {
        Case made = ofNoNumber(1);
        assertInstanceOf(TermRealizations.Realization.None.class,
                composed(made, made.measuring().region()));
    }

    @Test
    void whereANumberIsLeftTheContainerOfNoneMeetsACountOfNoneAsWell() {
        Case made = ofNumbers(0);
        TermRealizations.Realization built = composed(made, made.measuring().region());
        assertTrue(holdsTheContainerOfNone(built), "the container of none is among them: "
                + built);
    }

    /** A rule holding the total to no number holds the container of none to it, whose total is
     *  nought. */
    @Test
    void whereNoTotalIsLeftTheContainerOfNoneIsNoContainerEither() {
        Case made = theCase(NO_TOTAL, "b.xs", null, 0);
        TermRealizations.Realization composed = composed(made, made.measuring().region());
        assertFalse(holdsTheContainerOfNone(composed), composed.toString());
        assertFalse(composed instanceof TermRealizations.Realization.Built, composed.toString());
    }

    /**
     * A region that took in a condition about an element is a region of the rows handing that
     * element on, which hold it: where the condition leaves the element no number, no row is
     * left, the container of none among them.
     */
    @Test
    void whereAnElementHandedOnTheWayIsLeftNoNumberTheContainerOfNoneIsNotLeftEither() {
        Case made = ofNumbers(0);
        SearchRegion handed = made.measuring().region()
                .assuming(new LinearForm<>(ExactRatio.of(-10), Map.of(made.number(),
                        ExactRatio.ONE)), Rel.GT).taken()
                .assuming(LinearForm.atom(made.number()), Rel.LT).taken();
        assertTrue(handed.emptiness().isPresent(), "the control: the region holds no row");
        TermRealizations.Realization composed = composed(made, handed);
        assertFalse(holdsTheContainerOfNone(composed), composed.toString());
    }
}
