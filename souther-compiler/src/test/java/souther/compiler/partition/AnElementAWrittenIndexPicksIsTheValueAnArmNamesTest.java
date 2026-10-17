package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The name a {@code Some} arm opens over {@code List.get(i, xs)} stands for the element {@code i}
 * picks, where {@code i} is a number written down and {@code xs} is written out up to that element
 * with each of them there on every run.
 *
 * <p>{@code match List.get(0, String.codePoints("0")) with | Some zero -> c - zero} is
 * {@code c - 48}, so a guard {@code digitValue(x) >= 5} is a line at {@code x = 53}. Where some
 * element up to the one picked is kept on a condition, which element the index picks turns on the
 * run, and nothing is said of the name.
 */
class AnElementAWrittenIndexPicksIsTheValueAnArmNamesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** A guard over {@code c - zero}, with {@code zero} what the arm opens over {@code picked}. */
    private static String guarded(String picked) {
        return """
                module probe

                data Bad

                let digitValue (c: Int, k: Int): Int =
                    match %s with
                        | Some zero -> c - zero
                        | None -> 0

                behavior check : (x: Int, k: Int) -> Int | Bad
                let check (x, k) = {
                    guard digitValue(x, k) >= 5 else Bad
                    0
                }
                """.formatted(picked);
    }

    @Test
    void theCodePointOfATextWrittenDownIsTheNumberTheArmNames() {
        assertEquals(Set.of("52", "53"),
                pointsOn(reportOf(guarded("List.get(0, String.codePoints(\"0\"))")), "check/x"),
                "the code point of \"0\" is forty-eight, so the guard is a line at fifty-three");
    }

    /** An arm no run takes is no stop for the one that is taken, whatever it is written as. */
    @Test
    void anArmThatAbortsIsNoStopForTheArmTaken() {
        assertEquals(Set.of("52", "53"), pointsOn(reportOf("""
                module probe

                data Bad

                let digitValue (c: Int): Int =
                    match List.get(0, String.codePoints("0")) with
                        | Some zero -> c - zero
                        | None -> unreachable "\\"0\\" has a code point"

                behavior check : (x: Int) -> Int | Bad
                let check (x) = {
                    guard digitValue(x) >= 5 else Bad
                    0
                }
                """), "check/x"), "the line is the one the Some arm draws");
    }

    @Test
    void anElementOfAListWrittenOutIsTheNumberTheArmNames() {
        assertEquals(Set.of("52", "53"),
                pointsOn(reportOf(guarded("List.get(0, [48])")), "check/x"),
                "the element at nought is forty-eight");
    }

    @Test
    void theIndexPicksTheElementItNamesAndNotTheFirst() {
        assertEquals(Set.of("53", "54"),
                pointsOn(reportOf(guarded("List.get(1, String.codePoints(\"01\"))")), "check/x"),
                "the element at one is the code point of \"1\", forty-nine");
    }

    @Test
    void aCodePointPastTheBasicPlaneIsOneNumber() {
        assertEquals(Set.of("128516", "128517"),
                pointsOn(reportOf(guarded("List.get(0, String.codePoints(\"😀\"))")),
                        "check/x"),
                "U+1F600 is one code point, 128512, and not the first of two UTF-16 units");
    }

    @Test
    void aTextAndAListReachedThroughNamesArePickedTheSameWay() {
        assertEquals(Set.of("52", "53"), pointsOn(reportOf("""
                module probe

                data Bad

                let zeroText = "0"

                let digitValue (c: Int): Int = {
                    let codes = String.codePoints(zeroText)
                    let first = 0
                    match List.get(first, codes) with
                        | Some zero -> c - zero
                        | None -> 0
                }

                behavior check : (x: Int, k: Int) -> Int | Bad
                let check (x, k) = {
                    guard digitValue(x) >= 5 else Bad
                    0
                }
                """), "check/x"), "the names are followed to what they were given");
    }

    /** A list that is an input is no list written out, and its element is no number this reads. */
    @Test
    void anElementOfAnInputIsNotAWrittenNumber() {
        assertEquals(Set.of(), pointsOn(reportOf("""
                module probe

                data Bad

                let digitValue (c: Int, xs: List<Int>): Int =
                    match List.get(0, xs) with
                        | Some zero -> c - zero
                        | None -> 0

                behavior check : (x: Int, xs: List<Int>) -> Int | Bad
                let check (x, xs) = {
                    guard digitValue(x, xs) >= 5 else Bad
                    0
                }
                """), "check/x"), "the line is wherever the input's first element puts it");
    }

    /** The element picked is itself kept on a condition, so on a run where {@code k} is at or above
     *  forty-eight there is no element at nought for the arm to open. */
    @Test
    void anElementKeptOnAConditionIsNotTheOneTheIndexPicks() {
        assertEquals(Set.of(), pointsOn(reportOf(guarded(
                        "List.get(0, List.filter(n -> n > k, [48]))")), "check/x"),
                "forty-eight is the element at nought only where it is kept");
    }

    /** The element picked is there on every run, and one before it is not: where the one before is
     *  dropped, forty-eight is the element at nought and the element at one is none. */
    @Test
    void anElementBeforeTheOnePickedKeptOnAConditionMovesIt() {
        assertEquals(Set.of(), pointsOn(reportOf(guarded(
                        "List.get(1, List.flatMap(p -> p, [List.filter(n -> n > k, [7]), [48]]))")),
                        "check/x"),
                "which element is at one turns on whether seven was kept");
    }

    /** The control for the two above: the same lists with nothing kept on a condition. */
    @Test
    void theSameListsWithNothingDroppedArePicked() {
        assertEquals(Set.of("52", "53"), pointsOn(reportOf(guarded(
                        "List.get(1, List.flatMap(p -> p, [[7], [48]]))")), "check/x"),
                "seven is there on every run, so forty-eight is the element at one");
    }

    /** The list is written out as far as the element picked, so what follows it is not walked. */
    @Test
    void aTextLongerThanAWalkWritesOutIsPickedFromAsFarAsTheIndex() {
        assertEquals(Set.of("52", "53"), pointsOn(reportOf(guarded(zeros(0, 2000))), "check/x"),
                "the element at nought is forty-eight, however long the text is");
    }

    @Test
    void anIndexPastTheFigureIsNotPickedAt() {
        assertEquals(Set.of(), pointsOn(reportOf(guarded(zeros(1024, 1025))), "check/x"),
                "the element at the figure is past what a walk writes out");
        assertEquals(Set.of("52", "53"), pointsOn(reportOf(guarded(zeros(1023, 1024))), "check/x"),
                "and the one before it is not");
    }

    /** The element at {@code index} of the code points of {@code length} noughts. */
    private static String zeros(int index, int length) {
        return "List.get(" + index + ", String.codePoints(\"" + "0".repeat(length) + "\"))";
    }

    /** Every value at or beside a line of the statement a row is owed at, on {@code axis}. */
    private static Set<String> pointsOn(JsonNode report, String axis) {
        Set<String> out = new TreeSet<>();
        for (JsonNode reading : readingsOn(report, axis)) {
            out.add(reading.path("against").asString());
        }
        return out;
    }

    private static List<JsonNode> readingsOn(JsonNode report, String axis) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, axis, out);
        return out;
    }

    private static void collect(JsonNode node, String axis, List<JsonNode> out) {
        if (node.isObject() && node.has("point") && node.has("readings")
                && "part_of_comparison".equals(
                        node.at("/obligationId/line/which/kind").asString())
                && Set.of("at_the_line", "beside_the_line").contains(
                        node.at("/obligationId/location/kind").asString())) {
            JsonNode reading = node.path("readings").get(0);
            if (reading.path("axis").asString().equals(axis)) {
                out.add(reading);
            }
        }
        node.forEach(child -> collect(child, axis, out));
    }

    private static JsonNode reportOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.errors().isEmpty(), () -> "compiles: " + compilation.errors()
                .stream().map(e -> e.diagnostic().code()).toList());
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }
}
