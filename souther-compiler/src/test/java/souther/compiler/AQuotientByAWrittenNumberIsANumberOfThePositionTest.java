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

    /** The rows the block offers at the four points of that line, answered. */
    private static final String AT_THE_SLOPED_LINE = """
            example f
                | (0, 29) -> true
                | (0, 30) -> false
                | (0, 28) -> true
                | (0, 31) -> false
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
     * A line the quotient stands on one side of is a line as much as one on a bare position, and
     * the rows owed at it are offered and answer it.
     *
     * <p>The comparison relates the position's own number to the quotient of another, so it divides
     * neither and draws a line between them — the answer a comparison of two positions gets, which
     * is now the answer this one gets too.
     *
     * <p><b>The whole way round, because drawing the line is not what the author asked for.</b> A
     * border with points nothing can be written at is where the rule stood before, one word better
     * off: the report would name a boundary and go on saying every point of it was undecided. So
     * what is asked here is that the block offers a row for each point and that writing them takes
     * the obligations away.
     */
    @Test
    void aLineWithAFractionalSlopeIsOfferedRowsThatAnswerIt() {
        String report = report(measured(A_SLOPED_LINE));
        assertFalse(report.contains("written in a form this compiler does not read"), report);
        assertTrue(report.contains("borders 1"), report);
        assertTrue(report.contains("obligations 0/4"), report);

        String block = block(measured(A_SLOPED_LINE));
        for (String row : List.of("| (0, 29)", "| (0, 30)", "| (0, 28)", "| (0, 31)")) {
            assertTrue(block.contains(row), () -> "a row at each point: " + block);
        }

        String answered = report(measured(A_SLOPED_LINE + AT_THE_SLOPED_LINE));
        assertTrue(answered.contains("obligations 4/4"),
                () -> "and the rows offered answer every one of them: " + answered);
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
        // The value, wherever in its line it sits. A row composed for a class as well carries the
        // class's name between the bar and the value, so what this is about is the value.
        assertTrue(block.contains("(20)"), () -> "a value whose quotient is ten: " + block);

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
     * Two numbers of one place are recognised, and the line between them is offered a row.
     *
     * <p>{@code x / 2 < x / 3} draws its line between two numbers of one position, and the values
     * that stand on it are solved for out of them: each quotient by a written number runs over a
     * run of the place, so what a value may be is the run the two leave between them. Minus two is
     * one — its half is minus one and its third is nought.
     *
     * <p>Held here because both halves of it are decisions. A row at the line says the solving ran;
     * the sentences that are pinned absent say what the report may no longer claim, which is that
     * no value can be written there and that this compiler has no way of writing one.
     */
    @Test
    void twoNumbersOfOnePlaceAreSolvedTogetherAndTheirLineIsOfferedARow() {
        String model = """
                module example.quotient

                behavior f : (x: Int) -> Bool
                let f (x) = {
                    guard x / 2 < x / 3 else false

                    true
                }
                """;
        String offered = block(measured(model));
        assertTrue(offered.contains("| ("), () -> "a row is offered at the line: " + offered);
        String report = report(measured(model));
        assertTrue(report.contains("borders 1"), report);
        // The sentences a reader may not be told. One says no value exists; the other is what this
        // compiler said while it had no way of solving a value out of several numbers of one
        // place, and a line it solves one for is told neither.
        assertFalse(report.contains("no value can be written"), report);
        assertFalse(report.contains("the values that answer several of their own numbers"), report);
        // What is left is the region between the lines, where the pairs of numbers this compiler
        // tries run out before one of them is a pair some value has. Said as the figure it is,
        // which is a number somebody raises — so whatever stopped short here says so.
        //
        // Counted as well as read, because every one of them saying so is true of none of them:
        // a point that stops saying it is a point this compiler settled, which is a change to
        // look at here rather than a check that quietly stops checking.
        List<String> stoppedShort = report.lines()
                .filter(line -> line.contains("nothing could show a row can be written"))
                .toList();
        assertEquals(1, stoppedShort.size(),
                () -> "one point is left, which is the region between the lines: " + report);
        assertTrue(stoppedShort.stream()
                        .allMatch(line -> line.contains("a figure of this compiler's is why")),
                () -> "and a figure of this compiler's is what it says: " + stoppedShort);
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
        for (String divisor : List.of("y", "0")) {
            String model = dividedBy(divisor, "");
            assertEquals(List.of(), axesOf(measured(model)),
                    () -> "nothing is divided by `" + divisor + "`: " + report(measured(model)));
            assertTrue(report(measured(model)).lines().anyMatch(line ->
                            line.contains("not read: comparison@")
                                    && line.contains("written in a form this compiler does not"
                                            + " read")),
                    () -> "and the rule says so: " + report(measured(model)));
        }
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
