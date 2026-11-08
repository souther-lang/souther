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
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element moved to come to a total keeps to its type, where the type ties the number moved to
 * another field of the element no statement reads: an amount is at most its cap.
 *
 * <p>The smallest case that asks it: one element above ten, in a container coming to fifty. The
 * oracle reads each container offered back, element by element, against the rule as written.
 */
class AnElementMovedToATotalKeepsToItsTypeTest {

    private static final String SOURCE = """
            module g

            data Line = { amount: Int, cap: Int } invariant amount <= cap

            data Ok

            behavior counted : (xs: List<Line>) -> Ok
            """;

    private static final Pattern ELEMENT =
            Pattern.compile("amount = (-?\\d+), cap = (-?\\d+)");

    @Test
    void everyContainerOfferedHoldsElementsWithinTheirCap() {
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
        TermPath amount = xs.element().then("amount");
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(amount);
        NumericTerm total = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(amount), Type.INT, rules.inners(),
                rules.symbols());
        Proposition aboveTen = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-10), Map.of(new DecisionAtom.OfTheInput(number), ExactRatio.ONE)),
                Rel.GT), true);
        RealizationTarget.ACount count = new RealizationTarget.ACount(CountedElements.of(
                "counted", new Quantity.HowManyMeet(new DecisionSubject.AnInput(xs), aboveTen),
                measuring, AnElementMeeting.UNREAD));
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        demands.put(count, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                new Level.OfTheQuantity(ExactRatio.ONE))), Count.of(1)));
        ContainerAsAWhole.ATotal fifty = new ContainerAsAWhole.ATotal(total,
                new NumericSet.At(Count.of(50)), Count.of(50), measuring.ordersOf(total));
        TermRealizations.Realization composed = CardinalityComposer.compose(
                input.typeAt(xs, rules), List.of(), xs, List.of(count), List.of(), demands, null,
                List.of(), List.of(fifty), measuring, measuring.region(), reading);
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class, composed, () -> composed.shortfall()
                        .toString());
        for (FixtureTemplate each : built.values()) {
            Matcher found = ELEMENT.matcher(each.text());
            boolean any = false;
            while (found.find()) {
                any = true;
                assertFalse(Long.parseLong(found.group(1)) > Long.parseLong(found.group(2)),
                        "an amount past its cap: " + each.text());
            }
            assertTrue(any, each.text());
        }
    }
}
