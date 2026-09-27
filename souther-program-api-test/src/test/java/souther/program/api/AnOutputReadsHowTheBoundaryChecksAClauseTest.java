package souther.program.api;

import souther.compiler.core.BoundaryCheck;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.ValueShape;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What an output that is not this compiler learns about how the boundary checks each clause.
 *
 * <p>A decoder reports a broken clause as the constraint the clause is stated as — a string short of
 * its minimum length, a map with too few entries — and only what no constraint states as the clause
 * itself. Which constraint a clause is was the checker's to decide, and an output that could read
 * only the condition would have to decide it again from the condition. So the answer crosses with
 * the clause, and what is held here is what it says: each clause on its own, in the order it is
 * declared, whatever the clauses before it are.
 */
class AnOutputReadsHowTheBoundaryChecksAClauseTest {

    private static final String MODULE = """
            module shop

            data Code = String
                invariant digits = List.all(c -> c <= 57, String.codePoints(value))
                invariant long = String.length(value) >= 3
                invariant bounded = String.length(value) <= 8 && List.all(c -> c >= 48, String.codePoints(value))

            data Sku = String
                invariant String.matches("[0-9]+", value)

            data Tally = Map<String, Int>
                invariant counted = Map.size(value) >= 1

            data Span =
                { from: Int
                , to: Int
                }
                invariant ordered = from <= to
            """;

    /** Checked once: every test reads a different declaration of the same module. */
    private static final CheckedModule SHOP = CheckedProgram.of(List.of(MODULE)).module("shop");

    private static List<BoundaryCheck> boundaryOf(String name) {
        for (CheckedData each : SHOP.data()) {
            if (each.name().name().equals(name)) {
                return assertInstanceOf(CheckedData.WithFields.class, each, name).invariants()
                        .stream().map(ValueShape.Invariant::boundary).toList();
            }
        }
        throw new AssertionError(name + " is not among this module's data");
    }

    /**
     * A clause no constraint states is its condition alone; one stated whole is its constraint alone,
     * though a clause checked as itself comes before it; one stated in part is both.
     */
    @Test
    void eachClauseSaysWhatItIsStatedAsOnItsOwn() {
        assertEquals(List.of(
                        BoundaryCheck.conditionOnly(),
                        new BoundaryCheck(List.of(new BoundaryConstraint.MinLength(3)), false),
                        new BoundaryCheck(List.of(new BoundaryConstraint.MaxLength(8)), true)),
                boundaryOf("Code"));
    }

    /** A pattern crosses as what it matches and as it was written, and not as any engine's text. */
    @Test
    void aPatternCrossesAsWhatItMeansAndHowItWasWritten() {
        List<BoundaryCheck> sku = boundaryOf("Sku");

        assertEquals(1, sku.size());
        assertFalse(sku.get(0).checkCondition(), "the pattern is the whole clause");
        BoundaryConstraint.Pattern pattern = assertInstanceOf(BoundaryConstraint.Pattern.class,
                sku.get(0).constraints().get(0));
        assertEquals("[0-9]+", pattern.written());
    }

    @Test
    void aMapsSizeIsAConstraintOfTheMap() {
        assertEquals(List.of(new BoundaryCheck(List.of(new BoundaryConstraint.MapMinSize(1)), false)),
                boundaryOf("Tally"));
    }

    /** A product's clauses are about its fields, and the boundary checks each of them whole. */
    @Test
    void aProductsClauseIsItsCondition() {
        assertEquals(List.of(BoundaryCheck.conditionOnly()), boundaryOf("Span"));
    }
}
