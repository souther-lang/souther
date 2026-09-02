package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A floor the carrier supplies and a floor a clause wrote are moved by one mechanism.
 *
 * <p>A length is never negative and nothing writes that down, so {@code String.length(value) /= 0}
 * takes the nought off a floor nobody wrote and the position starts at one. A written floor with
 * the same value taken off it comes to the same place. Neither is named in the rule that moves it:
 * what they have in common is being in what the other rules leave, and that is where the rule is
 * read against.
 *
 * <p>Two things are asked of each model and they are separate answers. What the rules leave the
 * position is the geometry, and it is the same for both. What is owed for it is the authored line,
 * and a model writing two clauses is not a model writing one — a check that folded the second into
 * the first would let an obligation be deduplicated away the day the two ranges agreed.
 */
class AFloorTheCarrierSuppliesIsMovedAsAWrittenOneIsTest {

    /** The floor is the carrier's: a length is never negative, and no clause says so. */
    private static final String CARRIERS = """
            data Subject = String
                invariant notBlank = String.length(value) /= 0
            """;

    /** The same, with the floor written out beside the rule that moves it. */
    private static final String WRITTEN = """
            data Subject = String
                invariant notNegative = String.length(value) >= 0
                invariant notBlank = String.length(value) /= 0
            """;

    /** And the same two, the other way round, as one clause of two conjuncts. */
    private static final String TURNED = """
            data Subject = String
                invariant both = String.length(value) /= 0 && String.length(value) >= 0
            """;

    /** The row the issue was written from: a border where there was none. */
    @Test
    void aHoleAtTheCarriersFloorLeavesABorderAtOne() {
        assertEquals(List.of("String.length(n) = 1"), bordersOf(CARRIERS),
                "the position starts at one, and one is a line somebody has to write a row at");
    }

    /** The geometry is one answer, whichever floor the model wrote. */
    @Test
    void theRulesLeaveThePositionTheSameRangeEitherWay() {
        assertEquals(rangeOf(CARRIERS), rangeOf(WRITTEN));
        assertEquals(rangeOf(CARRIERS), rangeOf(TURNED));
        assertEquals("Bounds[min=Endpoint[at=1, inclusive=true], max=null]",
                rangeOf(CARRIERS).toString(), "and the range is the one the rules leave");
    }

    /** Swapping the conjuncts moves neither the range nor what is owed. */
    @Test
    void writingTheConjunctsTheOtherWayRoundChangesNothing() {
        assertEquals(bordersOf(WRITTEN), bordersOf(TURNED));
    }

    /**
     * And the obligations are not one. Two clauses are two authored lines, and the row written for
     * one is no evidence about the other.
     *
     * <p>Held against the geometry above: the same range, and not the same debts. A check for the
     * first that read as a check for the second would let the two be folded together.
     */
    @Test
    void thesameRangeIsNotTheSameObligation() {
        assertNotEquals(owedBy(CARRIERS), owedBy(WRITTEN),
                "one model writes one clause about the length and the other writes two");
    }

    /**
     * A rule whose arithmetic no end was read from leaves its line where the plain one does.
     *
     * <p>{@code value * 2 >= 4} has a bare name on neither side, so the reading of ends made
     * nothing of it and every reader below was told the model bounds the value nowhere. What it
     * leaves the position is where the plain rule leaves it, and a row is owed at the same place.
     *
     * <p>Nothing inverts the {@code 2 *}. What the rule did is read from the values the rules leave
     * with it and without it, which is the same question a rule naming a value is asked.
     */
    @Test
    void aRuleWhoseArithmeticPlacedNoEndLeavesItsLineWhereThePlainOneDoes() {
        assertEquals(bordersOf("""
                data Subject = Int
                    invariant plain = value >= 2
                """), bordersOf("""
                data Subject = Int
                    invariant doubled = value * 2 >= 4
                """));
    }

    /** The same of a record's field, which is read through another walk. */
    @Test
    void aFieldsArithmeticLeavesItsLineWhereThePlainOneDoes() {
        assertEquals(bordersOf("""
                data Subject = { x: Int }
                    invariant plain = x >= 2
                """), bordersOf("""
                data Subject = { x: Int }
                    invariant doubled = x * 2 >= 4
                """));
    }

    /**
     * And a quantity over two coordinates is not read this way at all.
     *
     * <p>Such a rule divides neither of them, so an end attributed to it at either would be an end
     * of a number it does not divide. Its line is drawn as the relation it is, and a row is owed
     * there.
     */
    @Test
    void aQuantityOverTwoCoordinatesIsNoOnePositionsEnd() {
        assertEquals(List.of("n.lo = n.hi"), bordersOf("""
                data Subject = { lo: Int, hi: Int }
                    invariant ordered = lo <= hi
                """), "one line, where the pair parts, and no end at either of them");
    }

    /** What each border is called, in the order a report shows them. */
    private static List<String> bordersOf(String declaration) {
        return boundariesOf(declaration).stream().map(BorderAssessment::label).toList();
    }

    /** Which authored lines are owed a row, as the rules that drew them are named. */
    private static List<String> owedBy(String declaration) {
        return boundariesOf(declaration).stream()
                .map(each -> each.origin().toString()).toList();
    }

    private static List<BorderAssessment> boundariesOf(String declaration) {
        Compilation compilation = Compilation.ofSource(sourceOf(declaration), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.floor");
        if (boundaries == null) {
            throw new AssertionError("the model under test compiles: " + declaration);
        }
        return boundaries.values().stream().flatMap(List::stream).toList();
    }

    /** What the rules leave the position, once every one of them has been read. */
    private static NumericDomain.Bounds rangeOf(String declaration) {
        Compilation compilation = Compilation.ofSource(sourceOf(declaration), "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return InputDomain.of(spec, sigs.get("take"), symbols, ReadAs.THE_COMPILATION_DOES)
                .at(TermPath.of("n")).rangeLeft();
    }

    private static String sourceOf(String declaration) {
        return """
                module example.floor

                %s
                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(declaration);
    }
}
