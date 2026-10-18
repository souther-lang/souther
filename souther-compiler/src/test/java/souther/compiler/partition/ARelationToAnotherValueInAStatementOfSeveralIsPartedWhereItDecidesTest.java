package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation of the input to another value, read as one part of a statement of several, parts the
 * values that settle it by lines on the input, in the cases where the statement turns on it.
 *
 * <p>{@code i.n > (if o.open then w else 5)} states a line at five where the order is not open and
 * a relation to the greatest a walk has kept where it is. Every {@code n} at or below nought is
 * below what the walk keeps, so the relation is false there whatever the walk kept; the line that
 * parts those values is read where the order is open, and the place is not said to be one the
 * other value is not shown to reach.
 */
class ARelationToAnotherValueInAStatementOfSeveralIsPartedWhereItDecidesTest {

    private static final String DECLARATIONS = """
            module demo

            data Item = { n: Int }
                invariant n >= 0 && n <= 100
            data Order = { items: List<Item>, q: Int, floor: Int, open: Bool }
                invariant q >= 0 && floor >= 0
            """;

    @Test
    void theLinePartingWhatSettlesItIsReadWhereTheRelationDecides() {
        ComparisonAssessment.Several several = severalOf("""
                List.fold((w, i) -> if i.n > (if o.open then w else 5) then i.n else w,
                          0, o.items) <= 10""");
        ComparisonAssessment.Several.Part part = relationPart(several);
        ComparisonAssessment.AgainstAnotherValue relation =
                assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, part.line());
        assertFalse(relation.settling().isEmpty(), several::toString);
        assertTrue(part.cases().stream().anyMatch(each -> each.condition().key().contains("o.open")),
                () -> "it decides where the order is open: " + several);
        assertEquals(part.cases().size(), part.readings().size(), several::toString);
        assertTrue(several.whatEachPlaceIsLeftWith().stream().noneMatch(
                        each -> each.why() instanceof BlockReason.RelationNotShownToReachEveryValue),
                several::toString);
    }

    /**
     * The control: the value found is the greatest of numbers between nought and a hundred, which
     * this does not work out, so no value of {@code q} is shown to settle the relation, no line
     * is read in any case, and the place keeps its reason.
     */
    @Test
    void whereNothingIsShownToSettleItThePlaceKeepsItsReason() {
        ComparisonAssessment.Several several = severalOf("""
                Option.withDefault(0, List.find(x -> x > 3, List.map(i -> i.n, o.items)))
                    >= o.q""");
        ComparisonAssessment.Several.Part part = relationPart(several);
        assertTrue(assertInstanceOf(ComparisonAssessment.AgainstAnotherValue.class, part.line())
                .settling().isEmpty(), several::toString);
        assertEquals(List.of(), part.cases(), several::toString);
        assertTrue(several.whatEachPlaceIsLeftWith().stream().anyMatch(
                        each -> each.why() instanceof BlockReason.RelationNotShownToReachEveryValue),
                several::toString);
    }

    private static ComparisonAssessment.Several.Part relationPart(
            ComparisonAssessment.Several several) {
        return several.parts().stream()
                .filter(each -> each.line() instanceof ComparisonAssessment.AgainstAnotherValue)
                .findFirst().orElseThrow(() -> new AssertionError(several.toString()));
    }

    /** The statement of several that {@code condition}'s comparisons include. */
    private static ComparisonAssessment.Several severalOf(String condition) {
        return walked(condition).stream()
                .map(each -> assertInstanceOf(BoundaryPolicy.Standing.Admitted.class,
                        each.standing()).read())
                .filter(ComparisonAssessment.Several.class::isInstance)
                .map(ComparisonAssessment.Several.class::cast)
                .filter(several -> several.parts().stream().anyMatch(
                        each -> each.line() instanceof ComparisonAssessment.AgainstAnotherValue))
                .findFirst().orElseThrow(() -> new AssertionError(condition));
    }

    private static List<ComparisonReadings.Reading> walked(String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + """

                behavior f : (o: Order) -> Int
                let f (o) =
                    if (%s) then 1 else 0
                """.formatted(condition.indent(8).strip()), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return ComparisonReadings.of("f", analysis, read, reads).comparisons();
    }
}
