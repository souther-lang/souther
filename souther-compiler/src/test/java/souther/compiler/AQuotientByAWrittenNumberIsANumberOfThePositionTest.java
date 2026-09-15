package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard dividing a position by a number the reading has draws a line, and the rows are owed it.
 *
 * <p>A truncating quotient is not a form the affine walk composes — a divide is a step and not a
 * line — and nothing here says it is. What it is, is a number taken of one place, the way an hour
 * is a number taken of a time: read off the value standing there and answered for by a value that
 * can be built. So a rule written over it is a rule over two numbers and the arithmetic between
 * them stays affine, which is what puts the line back where the model drew it.
 *
 * <p>Which number of the place it is, is the divisor's to say. Two quotients of one position by two
 * different numbers are two numbers, and a line drawn on either falls on one of them.
 */
class AQuotientByAWrittenNumberIsANumberOfThePositionTest {

    /** The quotient itself compared against a written number, so the line falls on the quotient. */
    private static final String ON_THE_QUOTIENT = """
            module example.quotient

            behavior f : (x: Int) -> Bool
            let f (x) = {
                guard x / 2 >= 10 else false

                true
            }
            """;

    /** The row the block offers for the point where the quotient is ten, answered. */
    private static final String ANSWERED = """
            example f
                | (20) -> true
            """;

    /** A region bounded by a line with a fractional slope, which is how a model states one. */
    private static final String A_SLOPED_LINE = """
            module example.quotient

            behavior f : (x: Int, y: Int) -> Bool
            let f (x, y) = {
                guard y < (x / 2 + 30) else false

                true
            }
            """;

    /**
     * The quotient is a number of the position, and the guard on it draws a line.
     *
     * <p>Where the rule went unread the report said so and owed nothing: no border, no point, and
     * an author with a boundary to cover was told the compiler could not read the rule they wrote.
     */
    @Test
    void aGuardOnTheQuotientDrawsALineOnIt() {
        String report = report(measured(ON_THE_QUOTIENT));
        assertFalse(report.contains("written in a form this compiler does not read"), report);
        assertTrue(report.contains("borders 1"), report);
        assertEquals(List.of("f/Int.divide(x, 2)"), axesOf(measured(ON_THE_QUOTIENT)), report);
    }

    /**
     * A line the quotient stands on one side of is a line as much as one on a bare position.
     *
     * <p>The comparison relates the position's own number to the quotient of another, so it divides
     * neither and draws a line between them — the answer a comparison of two positions gets, which
     * is now the answer this one gets too.
     */
    @Test
    void aLineWithAFractionalSlopeIsALine() {
        String report = report(measured(A_SLOPED_LINE));
        assertFalse(report.contains("written in a form this compiler does not read"), report);
        assertTrue(report.contains("borders 1"), report);
    }

    /**
     * The row offered at a point of the quotient stands at it once it is written.
     *
     * <p>The whole of what makes this a measurement and not a name: a value is composed for a
     * number asked for — the number times the divisor — and the row it is written into reads back
     * as that number. A search that composed a value reading back as something else would offer a
     * row at an edge it does not stand on, and the report would go on saying the point was
     * undecided with a row sitting on the page.
     */
    @Test
    void theRowOfferedAtAPointOnTheQuotientStandsAtIt() {
        String block = block(measured(ON_THE_QUOTIENT));
        assertTrue(block.contains("| (20)"), () -> "a value whose quotient is ten: " + block);

        assertEquals(new ItemAssessment.Coverage.Hit(),
                coverageAt(measured(ON_THE_QUOTIENT + ANSWERED), "f/Int.divide(x, 2)", "10"),
                () -> report(measured(ON_THE_QUOTIENT + ANSWERED)));
    }

    /**
     * Two divisors are two numbers of one place, and each line falls on its own.
     *
     * <p>What names such a number is the operation, the place and what it was given beside it. The
     * last of those was not there while a taking was an operation applied to one value — a length,
     * an hour — and without it the quotient by two and the quotient by three are one subject: one
     * axis, two lines drawn on it, and a row written for either reported as standing at both.
     */
    @Test
    void twoDivisorsAreTwoNumbersOfOnePlace() {
        String model = """
                module example.quotient

                behavior f : (x: Int) -> Bool
                let f (x) = {
                    guard x / 2 >= 10 else false
                    guard x / 3 >= 10 else false

                    true
                }
                """;
        assertEquals(List.of("f/Int.divide(x, 2)", "f/Int.divide(x, 3)"),
                axesOf(measured(model)).stream().sorted().toList(), () -> report(measured(model)));
    }

    /**
     * A divisor the reading does not have as a number leaves the rule unread.
     *
     * <p>Which quotient of the position it is, is not settled: read as a term all the same, the
     * line would be drawn wherever the reader's own assumption put it. So the rule is reported as
     * one nothing here read, which is where every such rule already stood.
     */
    @Test
    void aDivisorTheReadingDoesNotHaveIsNotOneOfThese() {
        assertTrue(report(measured(dividedBy("y", ""))).contains("does not read"),
                () -> report(measured(dividedBy("y", ""))));
        assertTrue(report(measured(dividedBy("0", ""))).contains("does not read"),
                () -> report(measured(dividedBy("0", ""))));
    }

    /**
     * And a name given a number is that number.
     *
     * <p>What the divisor reads as is the reading's answer and not how it was spelled, so a model
     * that names its divisor is measured as one that writes it out. Held here because the identity
     * of the number turns on it: read by spelling, the same quotient written two ways would be two
     * numbers of one place and a line drawn on either would fall on neither.
     */
    @Test
    void aNameGivenANumberIsThatDivisor() {
        assertEquals(List.of("f/Int.divide(x, 2)"),
                axesOf(measured(dividedBy("TWO", "let TWO = 2\n"))),
                () -> report(measured(dividedBy("TWO", "let TWO = 2\n"))));
    }

    /** The same model with the divisor written {@code divisor}, under whatever {@code names} it. */
    private static String dividedBy(String divisor, String names) {
        return """
                module example.quotient
                %s
                behavior f : (x: Int, y: Int) -> Bool
                let f (x, y) = {
                    guard x / %s >= 10 else false

                    true
                }
                """.formatted(names, divisor);
    }

    /** The axes the rules of the one behavior divide, named as the report names them. */
    private static List<String> axesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.quotient");
        return boundaries == null ? List.of()
                : boundaries.getOrDefault("f", List.of()).stream()
                        .map(each -> each.border().axis()).distinct().toList();
    }

    /** What the rows established at the point of {@code axis} against {@code value}. */
    private static ItemAssessment.Coverage coverageAt(Compilation compilation, String axis,
                                                      String value) {
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.quotient");
        return BorderAssessment.pointsOf(boundaries.get("f")).stream()
                .filter(p -> p.owed() != null)
                .filter(p -> p.border().axis().equals(axis) && value.equals(p.against()))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no point at " + axis + " = " + value))
                .owed().coverage().made().orElseThrow();
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.quotient")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
