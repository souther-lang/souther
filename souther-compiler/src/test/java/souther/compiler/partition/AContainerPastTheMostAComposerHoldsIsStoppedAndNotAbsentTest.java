package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
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

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container the rules hold to more elements than a count is composed with is one the figure
 * stopped, and not one the model has none of: seventeen numbers, one of them above half of what
 * they come to — a hundred and sixteen noughts — is a container, and the composer, held to
 * sixteen, says so as the figure it stopped at.
 */
class AContainerPastTheMostAComposerHoldsIsStoppedAndNotAbsentTest {

    @Test
    void seventeenNumbersOneAboveHalfOfTheirTotalAreStoppedAtTheFigure() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Box = { xs: List<Int> } invariant List.length(xs) >= 17

                data Ok

                behavior counted : (b: Box) -> Ok
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(compilation.db().ask(
                        new Bodies.DeclaredSignatures(module)).value().get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals("b.xs")).findFirst().orElseThrow();
        Quantities measuring = input.quantities(rules);
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(xs.element());
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(xs.element()), Type.INT, rules.inners(),
                rules.symbols());
        // the total less twice the number is below nought
        Proposition above = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.ZERO, Map.of(new DecisionAtom.OfTheInput(total), ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(number), ExactRatio.of(-2))), Rel.GE), false);
        RealizationTarget.ACount count = new RealizationTarget.ACount(CountedElements.of(
                "counted", new Quantity.HowManyMeet(new DecisionSubject.AnInput(xs), above),
                measuring, AnElementMeeting.UNREAD));
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        demands.put(count, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                new Level.OfTheQuantity(ExactRatio.ONE))), Count.of(1)));
        TermRealizations.Realization composed = CardinalityComposer.compose(
                input.typeAt(xs, rules), List.of(), xs, List.of(count), List.of(), List.of(), demands, null,
                List.of(), List.of(), measuring, measuring.region(), reading);
        TermRealizations.Realization.Stopped stopped = assertInstanceOf(
                TermRealizations.Realization.Stopped.class, composed, composed::toString);
        assertTrue(stopped.met().figures().contains(
                CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH), stopped.toString());
    }
}
