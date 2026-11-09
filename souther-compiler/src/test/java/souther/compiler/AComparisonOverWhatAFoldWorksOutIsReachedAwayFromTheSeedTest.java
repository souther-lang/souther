package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of what a fold works out over a list is reached at totals away from the seed, though
 * every element of the list is one the element type allows and the plain value of it adds nothing.
 *
 * <p>The candidates write a list at one size with its elements alike, which reaches a total only
 * at a multiple of the plain value. A point past that is reached by a row beside the ones that
 * ran: the list with an element put in it or changed for one a row of the module ran, whose run
 * the point is read off.
 */
class AComparisonOverWhatAFoldWorksOutIsReachedAwayFromTheSeedTest {

    private static final Pattern OFFERED = Pattern.compile(
            "// fills (ON|OFF|OUT) point of comparison[^\\n]*\\n\\s*\\| \\((?:Hand\\()?\\[([^\\]]*)\\]");

    private static final Pattern GUARDED = Pattern.compile(
            "// fills (ON|OFF|OUT) point of comparison@\\d+:\\d+:(\\d+)\\n\\s*\\| \\(\\[([^\\]]*)\\],"
                    + " (-?\\d+)\\)");

    private static final Pattern POINT = Pattern.compile("Points\\((\\d+)\\)");

    private static String scorer(String parameter, String list, int least, int target) {
        return scorer(parameter, list, least, target, "");
    }

    private static String scorer(String parameter, String list, int least, int target,
                                 String alsoRequired) {
        return """
                module m

                data Points = Int
                    invariant value >= %d && value <= 12%s

                data Score = Int
                    invariant value >= 0 && value <= 50
                %s
                behavior add : (s: Score, p: Points) -> Score

                let add (s, p) = {
                    let t = s.value + p.value
                    if t > 50 then Score(25) else Score(t)
                }

                example add
                    | (Score(48), Points(4)) -> Score(25)
                    | (Score(48), Points(2)) -> Score(50)
                    | (Score(0), Points(%d)) -> Score(%d)
                    | (Score(40), Points(12)) -> Score(25)
                    | (Score(38), Points(12)) -> Score(50)
                    | (Score(25), Points(10)) -> Score(35)
                    | (Score(46), Points(4)) -> Score(50)

                behavior total : (ps: List<Points>) -> Score

                let total (ps) = List.fold((s, p) -> add(s, p), Score(0), ps)

                example total
                    | ([]) -> Score(0)

                behavior reached : (%s) -> Bool

                let reached (ps) = total(%s).value == %d

                example reached
                    | (%s) -> false
                """.formatted(least, alsoRequired, parameter, least, least,
                parameter.isEmpty() ? "ps: List<Points>" : "ps: Hand",
                parameter.isEmpty() ? "ps" : "ps.value", target,
                list);
    }

    private static String scorer(int least, int target) {
        return scorer("", "[]", least, target);
    }

    /** The list of at most three that the element type's own rule allows. */
    private static String handOfAtMostThree(int target) {
        return scorer("""

                data Hand = List<Points>
                    invariant List.length(value) <= 3
                """, "Hand([])", 0, target);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static List<String> openPointsOf(String source, String behavior) {
        Compilation compilation = measured(source);
        List<String> lines = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
        int from = IntStream.range(0, lines.size())
                .filter(at -> lines.get(at).startsWith(behavior + " ")
                        && lines.get(at).contains("implemented"))
                .findFirst().orElseThrow();
        return lines.subList(from + 1, lines.size()).stream()
                .takeWhile(line -> !line.contains("implemented") && !line.startsWith("declarations"))
                .filter(line -> line.startsWith("? nothing could show a row can be written"))
                .toList();
    }

    /** What the rows offered for the points of `reached` are: the point, and the elements. */
    private static Map<String, List<List<Integer>>> offeredFor(String source) {
        Compilation compilation = measured(source);
        String block = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).textInEnglish();
        Map<String, List<List<Integer>>> out = new java.util.LinkedHashMap<>();
        Matcher row = OFFERED.matcher(block);
        while (row.find()) {
            List<Integer> elements = new ArrayList<>();
            Matcher point = POINT.matcher(row.group(2));
            while (point.find()) {
                elements.add(Integer.valueOf(point.group(1)));
            }
            out.computeIfAbsent(row.group(1), _ -> new ArrayList<>()).add(elements);
        }
        return out;
    }

    /** What `total` works out of the elements: the model's own fold, run here. */
    private static int totalOf(List<Integer> elements) {
        int score = 0;
        for (int each : elements) {
            int t = score + each;
            score = t > 50 ? 25 : t;
        }
        return score;
    }

    /** Totals of twenty, one either side, and past it are reached by rows of unlike elements. */
    @Test
    void everyPointOfATotalAwayFromTheSeedIsReached() {
        assertEquals(List.of(), openPointsOf(scorer(0, 20), "reached"));
    }

    /**
     * The rows offered are rows whose run comes out at each point: the total the model works out
     * of them is the level the point is at, and not a total some other row came to.
     */
    @Test
    void theRowOfferedForEachPointComesOutAtThePoint() {
        Map<String, List<List<Integer>>> offered = offeredFor(scorer(0, 20));

        assertEquals(List.of(20), offered.get("ON").stream().map(
                AComparisonOverWhatAFoldWorksOutIsReachedAwayFromTheSeedTest::totalOf).toList());
        assertEquals(List.of(19, 21), offered.get("OFF").stream().map(
                AComparisonOverWhatAFoldWorksOutIsReachedAwayFromTheSeedTest::totalOf)
                .sorted().toList());
        List<Integer> out = offered.get("OUT").stream().map(
                AComparisonOverWhatAFoldWorksOutIsReachedAwayFromTheSeedTest::totalOf).toList();
        assertEquals(1, out.size(), out.toString());
        assertTrue(out.getFirst() > 21 && out.getFirst() <= 50, out.toString());
    }

    /**
     * A comparison several conditions lead to is reached along either, and a row made beside one
     * that ran may go in by the other. What makes it a row of the point is that its run came out
     * at the level at the comparison, and not the way it went in: each row offered still comes
     * out at its level by the model's own fold, and still goes through the guard.
     */
    @Test
    void aRowBesideOneThatRanMayGoInByAnotherWayAndStillComesOutAtThePoint() {
        String source = scorer(0, 20)
                .replace("behavior reached : (ps: List<Points>) -> Bool",
                        "behavior reached : (ps: List<Points>, n: Int) -> Bool")
                .replace("let reached (ps) = total(ps).value == 20",
                        "let reached (ps, n) = if n == 1 || n == 2 then total(ps).value == 20"
                                + " else false")
                .replace("| ([]) -> false", "| ([], 1) -> false");
        Compilation compilation = measured(source);
        String block = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).textInEnglish();

        // The guard is two comparisons of its own, with points of their own; the one the fold is
        // compared at is the last in the line.
        List<Matcher> rows = new ArrayList<>();
        Matcher found = GUARDED.matcher(block);
        while (found.find()) {
            rows.add(GUARDED.matcher(found.group()));
            rows.getLast().matches();
        }
        int foldColumn = rows.stream().mapToInt(each -> Integer.parseInt(each.group(2))).max()
                .orElseThrow();
        int seen = 0;
        for (Matcher row : rows) {
            if (Integer.parseInt(row.group(2)) != foldColumn) {
                continue;
            }
            List<Integer> elements = new ArrayList<>();
            Matcher point = POINT.matcher(row.group(3));
            while (point.find()) {
                elements.add(Integer.valueOf(point.group(1)));
            }
            int n = Integer.parseInt(row.group(4));
            assertTrue(n == 1 || n == 2, "goes through the guard: " + row.group());
            int total = totalOf(elements);
            switch (row.group(1)) {
                case "ON" -> assertEquals(20, total, row.group());
                case "OFF" -> assertTrue(total == 19 || total == 21, row.group());
                default -> assertTrue(total > 21 && total <= 50, row.group());
            }
            seen++;
        }
        assertEquals(4, seen, block);
    }

    /** A least of one for the element makes a total of eight a row of unlike elements too. */
    @Test
    void aTotalMoreThanTheSizesTheCandidatesWriteIsReached() {
        assertEquals(List.of(), openPointsOf(scorer(1, 8), "reached"));
    }

    /**
     * A type that allows only some of the sizes the candidates are written at leaves the asking
     * of the candidates with nothing more to give before it has run them all. The rows beside the
     * ones that did run are looked at all the same.
     */
    @Test
    void aTypeThatAllowsOnlySomeSizesIsStillLookedBesideTheRowsThatRan() {
        String source = handOfAtMostThree(20);

        assertEquals(List.of(), openPointsOf(source, "reached"));
        offeredFor(source).values().stream().flatMap(List::stream)
                .forEach(row -> assertTrue(row.size() <= 3, row.toString()));
    }

    /**
     * A total no list comes to is not found, and is not said to be unreachable either: the report
     * names the rows that were made. The points are even and the score resets to an odd number
     * above twenty-one, so no row comes to twenty-one, and nothing in the types shows it.
     */
    @Test
    void aPointNoRowReachesIsOpenAndSaysWhatWasMade() {
        List<String> open = openPointsOf(
                scorer("", "[]", 0, 21, " && Int.floorMod(value, 2) == 0"), "reached");
        assertTrue(!open.isEmpty(), open.toString());
        assertTrue(open.stream().allMatch(line -> line.contains("then rows beside those")),
                open.toString());
        // And the search was cut by the figure of what it makes beside the rows run — the one
        // thing that stopped it, since nothing is there to be found — which the report names.
        assertTrue(open.stream().allMatch(line -> line.contains(
                        "how many candidates beside the rows run are made for a point")),
                open.toString());
    }
}
