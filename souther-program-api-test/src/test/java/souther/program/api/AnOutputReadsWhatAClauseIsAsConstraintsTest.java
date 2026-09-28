package souther.program.api;

import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.ConstraintProjection;
import souther.compiler.core.ValueShape;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.regex.PatternMeaning;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternRead;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output that is not this compiler learns about what each clause is as standard
 * constraints.
 *
 * <p>A newtype's decoder reports a broken clause as the constraint the clause is — a string short of
 * its minimum length, a map with too few entries — and only what no constraint is as the clause
 * itself. Which constraint a clause is was the checker's to decide, and an output that could read
 * only the condition would have to decide it again from the condition. So the answer crosses with
 * the clause, and what is held here is what it says: each clause on its own, whatever the clauses
 * before it are, and the same whichever form the data was declared in.
 */
class AnOutputReadsWhatAClauseIsAsConstraintsTest {

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

            data Label = { value: String }
                invariant digits = List.all(c -> c <= 57, String.codePoints(value))
                invariant long = String.length(value) >= 3
                invariant bounded = String.length(value) <= 8 && List.all(c -> c >= 48, String.codePoints(value))

            data Handle = { id: String }
                invariant String.length(id) >= 3
            """;

    /** Checked once: every test reads a different declaration of the same module. */
    private static final CheckedModule SHOP = CheckedProgram.of(List.of(MODULE)).module("shop");

    private static List<ConstraintProjection> projectionOf(String name) {
        for (CheckedData each : SHOP.data()) {
            if (each.name().name().equals(name)) {
                return assertInstanceOf(CheckedData.WithFields.class, each, name).invariants()
                        .stream().map(ValueShape.Invariant::projection).toList();
            }
        }
        throw new AssertionError(name + " is not among this module's data");
    }

    /**
     * A clause no constraint is, is none; one that is a constraint whole is complete, though a clause
     * that is none comes before it; one that is a constraint in part is not complete.
     */
    @Test
    void eachClauseSaysWhatItIsOnItsOwn() {
        assertEquals(List.of(
                        ConstraintProjection.none(),
                        new ConstraintProjection(List.of(new BoundaryConstraint.MinLength(3)), true),
                        new ConstraintProjection(List.of(new BoundaryConstraint.MaxLength(8)), false)),
                projectionOf("Code"));
    }

    /**
     * A pattern crosses as what it matches and as it was written, and not as any engine's text.
     *
     * <p>What it matches is held to the language's own reading of the text, which is the meaning
     * every output runs. Reaching {@link PatternMeaning} from a checked program says nothing here:
     * a clause's condition reaches it too, so a constraint that carried an engine's regex beside it
     * would still reach it.
     */
    @Test
    void aPatternCrossesAsWhatItMeansAndHowItWasWritten() {
        List<ConstraintProjection> sku = projectionOf("Sku");

        assertEquals(1, sku.size());
        assertTrue(sku.get(0).complete(), "the pattern is the whole clause");
        BoundaryConstraint.Pattern pattern = assertInstanceOf(BoundaryConstraint.Pattern.class,
                sku.get(0).constraints().get(0));
        assertEquals("[0-9]+", pattern.written());
        PatternRead.Read read = assertInstanceOf(PatternRead.Read.class,
                PatternParser.read("[0-9]+"));
        assertEquals(read.meaning(), pattern.meaning());
    }

    /**
     * What a clause is as constraints is about the value and not about how it crosses: a product of
     * one field holds the same clauses of the same field as a newtype does, and is answered alike.
     * That its constraints are not what its boundary checks is its form's to say.
     */
    @Test
    void aProductOfOneFieldIsAnsweredAsTheNewtypeItIsMadeLike() {
        assertEquals(projectionOf("Code"), projectionOf("Label"));
    }

    /** The field is the one the clause reads, whatever it is called. */
    @Test
    void aClauseIsReadOfTheOneFieldWhateverItIsCalled() {
        assertEquals(List.of(new ConstraintProjection(
                        List.of(new BoundaryConstraint.MinLength(3)), true)),
                projectionOf("Handle"));
    }

    /** A map's bound at one entry is its emptiness, as a list's is. */
    @Test
    void aMapsSizeIsAConstraintOfTheMap() {
        assertEquals(List.of(new ConstraintProjection(
                        List.of(new BoundaryConstraint.MapNonEmpty()), true)),
                projectionOf("Tally"));
    }

    /** A data of more than one field has no one field for a constraint to be about. */
    @Test
    void aClauseOfManyFieldsIsNone() {
        assertEquals(List.of(ConstraintProjection.none()), projectionOf("Span"));
    }
}
