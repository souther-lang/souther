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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The container of none is a container whether or not an element can be: where the region leaves
 * a number to no element, a count of none is still met by it, and a count of one is met by no
 * container at all — which is said as that, and not as a search stopped at the totals it tried,
 * since no total turns on an element there is none of.
 *
 * <p>The smallest case that asks it: a list of whole numbers, and how many of them are above half
 * of what they come to.
 */
class TheContainerOfNoneIsComposedWhetherOrNotAnElementCanBeTest {

    private static final String SOURCE = """
            module g

            data Ok

            behavior counted : (xs: List<Int>) -> Ok
            """;

    /** The input of {@link #SOURCE}, read, and the count of its numbers above half of their sum. */
    private record Case(Quantities measuring, RuleReadingContext reading, TermPath xs,
                        NumericTerm.ValueOf number, RealizationTarget.ACount count,
                        SequencedMap<RealizationTarget, AskedAt> demands) {}

    private static Case theCase(long asked) {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals("xs")).findFirst().orElseThrow();
        Quantities measuring = input.quantities(rules);
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(xs.element());
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(xs.element()), Type.INT, rules.inners(),
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
        return new Case(measuring, reading, xs, number, count, demands);
    }

    /** The region with the number above ten and below nought, which no element is. */
    private static SearchRegion leavingNoNumber(Case made) {
        return made.measuring().region()
                .assuming(new LinearForm<>(ExactRatio.of(-10), Map.of(made.number(),
                        ExactRatio.ONE)), Rel.GT).taken()
                .assuming(LinearForm.atom(made.number()), Rel.LT).taken();
    }

    private static TermRealizations.Realization composed(Case made, SearchRegion region) {
        return CardinalityComposer.compose(new Type.ListOf(Type.INT), List.of(), made.xs(),
                List.of(made.count()), List.of(), made.demands(), null, List.of(), List.of(),
                made.measuring(), region, made.reading());
    }

    @Test
    void whereNoNumberIsLeftTheContainerOfNoneMeetsACountOfNone() {
        Case made = theCase(0);
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                leavingNoNumber(made).projectionOf(made.number()));
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class, composed(made, leavingNoNumber(made)));
        assertEquals(1, built.values().size(), "the container of none, and no other");
    }

    @Test
    void whereNoNumberIsLeftNoContainerMeetsACountOfOne() {
        Case made = theCase(1);
        assertInstanceOf(TermRealizations.Realization.None.class,
                composed(made, leavingNoNumber(made)));
    }

    @Test
    void whereANumberIsLeftTheContainerOfNoneMeetsACountOfNoneAsWell() {
        Case made = theCase(0);
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class,
                composed(made, made.measuring().region()));
        assertTrue(built.values().size() >= 1, "the container of none is among them");
    }
}
