package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeCardinality;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The elements of a container composed for a count keep to their type whatever number the count
 * puts them at, where the type ties the number to a position the statement may or may not read:
 * an amount above a hundred is only active.
 *
 * <p>The smallest case that asks it: one element above a hundred, and above half of the total.
 */
class TheElementsOfAKindKeepToTheTypeWhateverTheNumberIsTest {

    private static final String SOURCE = """
            module g

            data Forecast = { amount: Int, active: Bool } invariant amount <= 100 || active

            data Ok

            behavior counted : (xs: List<Forecast>) -> Ok
            """;

    private static final Pattern ELEMENT =
            Pattern.compile("amount = (-?\\d+), active = (true|false)");

    /** Containers meeting a count of one, of the elements above a hundred and above half of the
     *  total — and, where {@code readsActive}, active too. */
    private static TermRealizations.Realization.Built composed(boolean readsActive) {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        Position list = input.positions().stream()
                .filter(each -> each.path().toString().equals("xs")).findFirst().orElseThrow();
        TermPath xs = list.path();
        Quantities measuring = input.quantities(rules);
        TermPath amount = xs.element().then("amount");
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(amount);
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(amount), Type.INT, rules.inners(),
                rules.symbols());
        // above a hundred, and the total less twice the number is below nought
        Proposition aboveAHundred = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-100), Map.of(new DecisionAtom.OfTheInput(number), ExactRatio.ONE)),
                Rel.GT), true);
        Proposition aboveHalf = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.ZERO, Map.of(new DecisionAtom.OfTheInput(total), ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(number), ExactRatio.of(-2))), Rel.GE), false);
        List<Proposition> parts = new java.util.ArrayList<>(List.of(aboveAHundred, aboveHalf));
        if (readsActive) {
            parts.add(new Proposition.Truth(new DecisionSubject.AnInput(
                    xs.element().then("active")), true));
        }
        CardinalityComposer.Asked.SoManyMeeting many = new CardinalityComposer.Asked.SoManyMeeting(
                AStatementAtARow.of(Proposition.all(parts), "counted", measuring),
                LevelRegion.point(new Level.OfTheQuantity(ExactRatio.ONE)), Optional.empty(),
                Optional.empty());
        CoupledCardinalityComposer.Coupled coupled =
                CoupledCardinalityComposer.Coupled.of(List.of(many), xs, measuring);
        assertTrue(coupled != null, "the count is one the composition takes");
        TypeView view = TypeView.of(list.type(), rules.inners(), rules.symbols(), rules.kinds(),
                rules.sums());
        return assertInstanceOf(TermRealizations.Realization.Built.class,
                CoupledCardinalityComposer.compose(coupled, xs, null, list.type(),
                        (Shape.Sequence) view.shape(), measuring, measuring.region(), reading));
    }

    /** Whether every element of the container is active or at most a hundred, and there is one. */
    private static boolean keepsToTheType(FixtureTemplate container) {
        Matcher found = ELEMENT.matcher(container.text());
        boolean any = false;
        while (found.find()) {
            any = true;
            if (Integer.parseInt(found.group(1)) > 100 && !"true".equals(found.group(2))) {
                return false;
            }
        }
        return any;
    }

    /**
     * The containers offered are proposals the rows are run on, and the type decides which stand:
     * among them is one whose every element keeps to it, however the number puts it past a
     * hundred.
     */
    @Test
    void aContainerKeepingToTheTypeIsAmongThoseOfferedWhereTheStatementDoesNotReadThePosition() {
        assertTrue(composed(false).values().stream()
                .anyMatch(TheElementsOfAKindKeepToTheTypeWhateverTheNumberIsTest::keepsToTheType),
                "a container within the type is offered");
    }

    @Test
    void aContainerKeepingToTheTypeIsAmongThoseOfferedWhereTheStatementReadsThePosition() {
        assertTrue(composed(true).values().stream()
                .anyMatch(TheElementsOfAKindKeepToTheTypeWhateverTheNumberIsTest::keepsToTheType),
                "a container within the type is offered");
    }
}
