package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class of a number taken of a position is offered a value by whatever offers one at a point of
 * it, so the account the point was written for is the account the class is filled for.
 *
 * <p>Two readers wrote a value for such a number and only one of them asked what the number was
 * taken as. The points came from the reader with an arm per account; the classes came from a second
 * one that took every number of a position for a count of what it holds, and built a value holding
 * that many. So an hour of nine asked for a time holding nine of something, no time holds any, and
 * the class was reported as one nothing writes a value for — a shortfall of this compiler's, in
 * words that read as one about the model.
 *
 * <p>The two models below are the two ways that went wrong, and they fail differently. A part of a
 * time is a number no count answers at all, so the class came back with nothing. A total is a number
 * a count is shaped like: a value holding eight elements was built where a value whose elements come
 * to eight was asked for, and it was offered as the class's own — which is the worse of the two,
 * because the row is there and reads back as a number the class was not built at.
 */
class AClassOfATakenNumberIsFilledByWhatFillsAPointOfItTest {

    /** A part of a time, which is a number nothing holding that many answers. */
    private static final String AN_HOUR = """
            module example.taken

            behavior f : (t: Time) -> Bool
            let f (t) = {
                guard Time.hour(t) >= 9 else false

                true
            }
            """;

    /** The rows the block offers for that model's classes, answered. */
    private static final String AN_HOUR_ANSWERED = """
            example f
                | (Time("00:00:00")) -> false
                | (Time("09:00:00")) -> true
            """;

    /** A total, which is a number a count is shaped like and is not. */
    private static final String A_TOTAL = """
            module example.taken

            behavior g : (ns: List<Int>) -> Bool
            let g (ns) = {
                guard List.sum(ns) >= 9 else false

                true
            }
            """;

    /** The rows the block offers for that model's classes, answered. */
    private static final String A_TOTAL_ANSWERED = """
            example g
                | ([8]) -> false
                | ([9]) -> true
            """;

    /** A rule that singles one number out rather than drawing a line, over a part of a time. */
    private static final String AN_HOUR_SINGLED_OUT = """
            module example.taken

            behavior k : (t: Time) -> Bool
            let k (t) = {
                guard Time.hour(t) /= 9 else false

                true
            }
            """;

    /** The same over a total, which is the other account a count is shaped like. */
    private static final String A_TOTAL_SINGLED_OUT = """
            module example.taken

            behavior m : (ns: List<Int>) -> Bool
            let m (ns) = {
                guard List.sum(ns) /= 9 else false

                true
            }
            """;

    /** A class of counts higher than what its position holds any of, which this compiler tries a
     *  few of and gives up on. */
    private static final String MORE_THAN_IT_HOLDS = """
            module example.taken

            behavior h : (s: Set<Bool>) -> Bool
            let h (s) = {
                guard Set.size(s) >= 3 else false

                true
            }
            """;

    /**
     * A class of the hour is offered a time standing in it.
     *
     * <p>Both halves, because either alone would pass over the defect. That a row is offered says
     * the class reached the reader that knows what an hour is written into; that writing the rows
     * closes the partition says the times offered read back as hours inside the classes they were
     * offered for.
     */
    @Test
    void aClassOfAPartOfATimeIsOfferedATimeStandingInIt() {
        assertEquals(Map.of("t=0 <= x < 9", "Time(\"00:00:00\")",
                        "t=9 <= x <= 23", "Time(\"09:00:00\")"),
                offeredForEachClass(AN_HOUR, "f"));

        String report = report(AN_HOUR + AN_HOUR_ANSWERED);
        assertTrue(report.contains("equivalence partitions 2/2"), report);
    }

    /**
     * And a class of the total is offered a list whose elements come to a number inside it.
     *
     * <p>Where the one above came back with nothing, this one came back with a value: a list of
     * eight elements for the class below nine, whose total is nought. The class it was offered for
     * holds it, which is why nothing said anything — and the class above nine was offered a list of
     * nine elements totalling nought, which that class does not hold.
     */
    @Test
    void aClassOfATotalIsOfferedAListWhoseElementsComeToIt() {
        assertEquals(Map.of("ns=x < 9", "[8]", "ns=9 <= x", "[9]"),
                offeredForEachClass(A_TOTAL, "g"));

        String report = report(A_TOTAL + A_TOTAL_ANSWERED);
        assertTrue(report.contains("equivalence partitions 2/2"), report);
    }

    /**
     * And a row holding that many elements does not stand in a class of what they come to.
     *
     * <p>The control the assertion above needs. Lists of eight and of nine elements are what a
     * reader taking the total for a count offers, and they are rows a model can hold — so a check
     * that only asked whether rows were offered would pass on them. What they leave is the class
     * above nine with nothing in it, since a list of nine noughts comes to nought.
     */
    @Test
    void aRowHoldingThatManyElementsDoesNotStandInAClassOfWhatTheyComeTo() {
        String report = report(A_TOTAL + """
                example g
                    | ([0, 0, 0, 0, 0, 0, 0, 0]) -> false
                    | ([0, 0, 0, 0, 0, 0, 0, 0, 0]) -> false
                """);

        assertTrue(report.contains("equivalence partitions 1/2"), report);
        assertTrue(report.contains("no row is in `List.sum(ns)/9 <= x`"), report);
    }

    /**
     * A class of a number a rule singled out is offered a value of the position, not the number.
     *
     * <p>The other shape a class of a number comes in, and one measured on its own rather than
     * beside a second number of the same location. A rule that names a number instead of drawing a
     * line leaves that number and everything else, and a value standing in either is built by what
     * builds a value at a number — the ninth hour is a time, and the number nine is not one.
     *
     * <p>The hour offered for everything but nine is the first hour a day has, because the part
     * walks the hours it runs between and asks the class which of them it admits. A number named
     * beside the class would have been one candidate; the account has the whole of its own kind.
     */
    @Test
    void aClassOfAPartOfATimeSingledOutIsOfferedATime() {
        assertEquals(Map.of("t== 9", "Time(\"09:00:00\")",
                        "t=/= 9", "Time(\"00:00:00\")"),
                offeredForEachClass(AN_HOUR_SINGLED_OUT, "k"));
    }

    /** And a class of a total singled out is offered a list coming to it. */
    @Test
    void aClassOfATotalSingledOutIsOfferedAList() {
        assertEquals(Map.of("ns== 9", "[9]", "ns=/= 9", "[10]"),
                offeredForEachClass(A_TOTAL_SINGLED_OUT, "m"));
    }

    /**
     * And a class this compiler stopped before reaching a value for is not one nothing writes a
     * value for.
     *
     * <p>The two sentences a class with no value can carry, and which of them it is turns on
     * whether the search looked everywhere. A set of truths holds two at most, so the counts this
     * class admits run past what this compiler tries and none of the ones it tried built — which is
     * this compiler giving up, not the position having no such value. Told the other way, an author
     * reads a shortfall of this compiler's as a fact about the model, which is what the classes of
     * a taken number were doing before any of this.
     */
    @Test
    void aClassNothingReachedAValueForDoesNotSayNothingWritesOne() {
        String block = offered(MORE_THAN_IT_HOLDS, "h");

        assertTrue(block.contains("nothing here composed a value whose Set.size is in this range,"
                + " which does not make one unwritable"), block);
        assertFalse(block.contains("nothing here writes a value whose Set.size"), block);
    }

    /**
     * What this compiler composed for each class of that behavior, by the class it composed it for.
     *
     * <p>Read off the purpose each row carries rather than out of the block. A row written for a
     * point of a border can fall in a class as well, so a block holding a value says nothing about
     * which class anything was composed for — which is how a class offered a list of eight noughts
     * passed beside the point rows that hold eight.
     */
    private static Map<String, String> offeredForEachClass(String source, String behavior) {
        Adequacy.Filling filling =
                Adequacy.generatedOf(measured(source).db(), "example.taken").get(behavior);
        assertNotNull(filling, "the behavior under test is generated for");
        Map<String, String> out = new LinkedHashMap<>();
        for (Generator.GeneratedRow row : filling.composed().rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass forAClass) {
                    out.put(forAClass.label(), row.inputs().get(0).text());
                }
            }
        }
        return out;
    }

    /** The rows this compiler offers for what nothing covers, and the sentences beside them. */
    private static String offered(String source, String behavior) {
        Compilation compilation = measured(source);
        return souther.compiler.report.GeneratedRows.of(compilation, "example.taken", behavior,
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    private static String report(String source) {
        Compilation compilation = measured(source);
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
