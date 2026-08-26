package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A run can stop where the order itself stops, and what reaches a border does not say which end is
 * which.
 *
 * <p>A length is never negative, and no clause of the model says so: it is what the operation taking
 * the length answers ({@link NumericTerm#intrinsicBounds}). What a position runs between is that
 * met with what the rules leave it, and the two arrive at a border as one pair of ends — so the end
 * a clause wrote and the end the order supplies are the same shape and are told apart by nothing.
 *
 * <p>Which matters to whoever is asked for a row inside the run. An end a declaration wrote is
 * something an author can move; an end the order supplies is not, and there is nobody to name for
 * it. Read off the value instead — this end is where the carrier stops, so nobody wrote it — a model
 * that does write {@code String.length(value) >= 0} would be read as having written nothing.
 */
class AnEndTheOrderSuppliesIsNotOneARuleWroteTest {

    /** One clause, stopping a length at nine and saying nothing about the other end. */
    private static final String LENGTH = """
            module example.extent

            data Name = String
                invariant String.length(value) <= 9

            data Ok

            behavior take : (n: Name) -> Ok
            let take (n) = Ok

            example take
                | "x" : (Name("abc")) -> Ok
            """;

    /**
     * The run below the line stops at both ends, and only one of them was written.
     *
     * <p>Nine is the clause's. Zero is the length's own floor, and the run carries it as an end just
     * as it carries the other.
     */
    @Test
    void aRunStopsAtAnEndNoClauseWrote() {
        BorderAssessment line = borderAt("String.length(n) = 9");
        Criterion criterion = line.border().demand(PointRole.IN).criterion();
        Criterion.Within inside = (Criterion.Within) criterion;

        assertEquals("take/String.length(n) in 0 <= String.length(n) < 9",
                said(line, PointRole.IN), "the run has both ends and the model wrote one of them");
        assertNotNull(inside.band().from(), "the low end is there");
        assertNotNull(inside.band().to(), "and so is the high one");
    }

    /**
     * And the low end is the one the operation answers, not the one the clause wrote.
     *
     * <p>Held against {@link NumericTerm#intrinsicBounds} rather than against the number, so that
     * what this says is where the end came from and not what it happens to be.
     */
    @Test
    void theLowEndIsTheOnesTheOperationAnswers() {
        BorderAssessment line = borderAt("String.length(n) = 9");
        Criterion.Within inside =
                (Criterion.Within) line.border().demand(PointRole.IN).criterion();
        NumericDomain.Bounds order = termOf(line).intrinsicBounds();

        assertNotNull(order.min(), "a length is never less than nothing, and nothing wrote that");
        assertEquals(0, inside.band().from().at().compare(order.min().at()),
                "which is where the run stops below");
        assertNull(order.max(), "the order says nothing about how long a string gets");
        assertNotNull(inside.band().to(),
                "and the run stops above all the same, where the clause put it");
    }

    /** A position's own value has no such end, so nothing about the position says one is coming. */
    @Test
    void aPositionsOwnValueHasNoEndOfItsOwn() {
        assertEquals(NumericDomain.Bounds.OPEN,
                new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("x"))
                        .intrinsicBounds(),
                "the order under a position runs as far as the carrier does");
    }

    private static NumericTerm termOf(BorderAssessment line) {
        if (!(line.border().cut().of() instanceof BorderQuantity.OfACoordinate one)) {
            throw new AssertionError("this line is not on a coordinate: " + line.border().cut());
        }
        return one.term();
    }

    private static String said(BorderAssessment line, PointRole role) {
        return line.points().stream().filter(point -> point.role() == role).findFirst()
                .orElseThrow(() -> new AssertionError("no " + role + " point")).said();
    }

    private static BorderAssessment borderAt(String label) {
        Compilation compilation = Compilation.ofSource(LENGTH, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.extent");
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.values().stream().flatMap(List::stream)
                .filter(each -> each.label().equals(label)).findFirst()
                .orElseThrow(() -> new AssertionError(label + " is not a line of this model: "
                        + boundaries.values().stream().flatMap(List::stream)
                                .map(BorderAssessment::label).toList()));
    }
}
