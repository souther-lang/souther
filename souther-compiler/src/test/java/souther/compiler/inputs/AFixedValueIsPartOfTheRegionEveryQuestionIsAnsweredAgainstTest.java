package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Fixing a position moves the region every question after it is answered against.
 *
 * <p>Not the term the question happens to name. A rule relating two positions is in neither of
 * their ranges, so what a form runs between depends on where the other positions were fixed, and an
 * assignment such a rule refuses is refused nowhere but against the whole of it. Read as a bound of
 * the asked-about term alone, a search asking where a companion may stand was told its own range
 * and placed a row the rule above it turned back.
 *
 * <p>The relations here are taken in rather than declared, which is the shape a condition on the way
 * to a border arrives in. What the declarations relate travels the same path once it is in the
 * rules — this is about the fixings reaching them at all.
 */
class AFixedValueIsPartOfTheRegionEveryQuestionIsAnsweredAgainstTest {

    /**
     * Three positions with no rule of their own, one to a parameter.
     *
     * <p>Separate parameters on purpose. What a caller fixes inside one value is already read with
     * that value's own rules, so a pair of fields is answered by a path that has nothing to do with
     * the region — and a model written that way is green whether or not a fixing ever reaches the
     * rules the relations are in.
     */
    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int, z: Int) -> Ok
            """;

    /** Where {@code x} runs once {@code y} is fixed above the line {@code y <= 2x} draws. */
    @Test
    void aFormRunsWhereTheFixedCompanionPutsIt() {
        NumericDomain.Bounds runs = runsBetween(
                related().given(term("y"), Count.of(BigDecimal.valueOf(100))), term("x"));

        assertNotNull(runs, "x is a number this reading answers about");
        assertNotNull(runs.min(), () -> "x starts where y <= 2x puts it once y stands, and runs "
                + runs);
        assertEquals("50", number(runs.min()),
                "y at 100 under y <= 2x leaves x at 50 and above");
    }

    /** And nothing else starts it, so the end above is the relation's doing. */
    @Test
    void andWithoutTheRelationNothingStartsIt() {
        NumericDomain.Bounds runs = runsBetween(
                region().given(term("y"), Count.of(BigDecimal.valueOf(100))), term("x"));

        assertTrue(runs == null || runs.min() == null,
                () -> "x is started by nothing once the relation is gone, and runs " + runs);
    }

    /**
     * And a placement the relation refuses is refused.
     *
     * <p>Which no range of either position holds: both values are inside what their own type and
     * their own rules leave, and it is the pair the relation is about.
     */
    @Test
    void anAssignmentTheRelationRefusesIsShownToLeaveNothing() {
        assertTrue(related()
                        .given(term("y"), Count.of(BigDecimal.valueOf(100)))
                        .given(term("x"), Count.of(BigDecimal.ZERO))
                        .emptiness().isPresent(),
                "y at 100 and x at 0 is refused by y <= 2x");
    }

    /** And one it admits is not. */
    @Test
    void andAnAssignmentItAdmitsIsNot() {
        assertFalse(related()
                        .given(term("y"), Count.of(BigDecimal.valueOf(100)))
                        .given(term("x"), Count.of(BigDecimal.valueOf(50)))
                        .emptiness().isPresent(),
                "y at 100 and x at 50 is on the line y <= 2x draws");
    }

    /**
     * And a fixing reaches a position no relation names it beside.
     *
     * <p>{@code z} is related to {@code x} by nothing written about the two of them: what carries
     * the value is {@code z <= y} and {@code y <= 2x} together. A reading that took in the fixings
     * of whatever a relation names directly would answer this one wide, which is the same defect
     * one step further out.
     */
    @Test
    void aFixingReachesWhatTheRelationsReachAndNotOnlyItsNeighbour() {
        NumericDomain.Bounds runs = runsBetween(
                related().assuming(minus("z", "y"), Rel.LE)
                        .given(term("z"), Count.of(BigDecimal.valueOf(100))), term("x"));

        assertNotNull(runs, "x is a number this reading answers about");
        assertNotNull(runs.min(), () -> "x starts where z <= y <= 2x puts it, and runs " + runs);
        assertEquals("50", number(runs.min()),
                "z at 100 under z <= y and y <= 2x leaves x at 50 and above");
    }

    /** Where the term runs, of a region that holds something — which every region here does. */
    private static NumericDomain.Bounds runsBetween(SearchRegion within,
                                                    NumericTerm.FromOnePosition term) {
        return switch (within.projectionOf(term)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) -> runs;
            case NumericDomain.FormProjection.NothingIsLeft _ ->
                    throw new AssertionError("these rules leave a value: " + term);
            case null -> null;
        };
    }

    /** The region with {@code y - 2x <= 0} taken in. */
    private static SearchRegion related() {
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(term("y"), BigDecimal.ONE);
        coefs.put(term("x"), BigDecimal.valueOf(-2));
        return region().assuming(new LinearForm<>(BigDecimal.ZERO, coefs), Rel.LE);
    }

    /** The form {@code one - other}. */
    private static LinearForm<NumericTerm> minus(String one, String other) {
        return LinearForm.<NumericTerm>atom(term(one))
                .minus(LinearForm.<NumericTerm>atom(term(other)));
    }

    /**
     * The model read once for the whole class.
     *
     * <p>Every question here is asked of one reading of one source, and reading it again per term
     * would compile this model once for each name a form is spelled with. Held as the reading and
     * the rules together because a region is made of both.
     */
    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static final Read READ = read();

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(pathOf(spelled));
    }

    private static String number(souther.compiler.numeric.Endpoint end) {
        return Count.number(end.at()).at().stripTrailingZeros().toPlainString();
    }

    private static TermPath pathOf(String spelled) {
        return READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + READ.input().positions().stream()
                                .map(Position::path).toList()));
    }

    private static Read read() {
        Compilation compilation =
                Compilation.ofSources(List.of(PAIR), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("read"), rules, ReadAs.THE_COMPILATION_DOES),
                rules);
    }
}
