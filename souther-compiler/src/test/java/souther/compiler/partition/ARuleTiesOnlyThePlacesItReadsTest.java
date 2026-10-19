package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two numbers under one input are tied by the declarations only where the rules around them chain
 * from one to the other. A rule that reads other fields of what it sits in ties neither.
 */
class ARuleTiesOnlyThePlacesItReadsTest {

    private static final String RELATES = "relates";

    private static final String NOT_READ = "not read";

    /** The word each place is left with by the one comparison in {@code source}, by its name. */
    private static Map<String, String> left(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, String> out = new LinkedHashMap<>();
        for (String line : report.lines().map(String::strip).toList()) {
            if (!line.contains("comparison@") || !line.contains("about `")) {
                continue;
            }
            if (!line.startsWith("· no line") && !line.startsWith("· not read")) {
                continue;
            }
            String place = line.substring(line.lastIndexOf("about `") + 7, line.length() - 1);
            out.put(place, line.startsWith("· not read") ? NOT_READ : RELATES);
        }
        return out;
    }

    private static String pair(String declarations, String body) {
        return """
                module w1
                %s
                data Ans = Yes | No
                behavior m : (x: R) -> Ans
                let m (x) = if %s then Yes else No
                """.formatted(declarations, body);
    }

    private static final String W = """
            data W = { v: Int }
                invariant v >= 0
            """;

    private static String elements(String declarations, String bookRule, String test) {
        return """
                module w2
                %s
                data Book = List<Wrapped>
                    invariant %s
                behavior m : (b: Book, k: Int) -> List<Wrapped>
                let m (b, k) = List.filter(c -> %s, b.value)
                """.formatted(declarations, bookRule, test);
    }

    @Test
    void aRuleOfTheTypeEachSitsInDoesNotTieTheTwo() {
        assertEquals(Map.of("x.a.v", RELATES),
                left(pair(W + "data R = { a: W, b: W }", "x.a.v < x.b.v")));
    }

    @Test
    void aRuleOfTheValueAroundBothTiesThem() {
        assertEquals(Map.of("x.a.v", NOT_READ, "x.b.v", NOT_READ),
                left(pair(W + "data R = { a: W, b: W } invariant a.v <= b.v",
                        "x.a.v < x.b.v")));
    }

    /** Neither rule reads both, and the two are tied through the place both of them read. */
    @Test
    void aRuleBetweenTheTwoTiesThemForAComparisonThatCanHold() {
        assertEquals(Map.of("x.a", NOT_READ, "x.b", NOT_READ), left(pair("""
                data R = { a: Int, b: Int }
                    invariant a >= b
                """, "x.a > x.b")));
    }

    @Test
    void twoRulesSharingAThirdPlaceTieTheOtherTwo() {
        assertEquals(Map.of("x.a", NOT_READ, "x.b", NOT_READ), left(pair("""
                data R = { a: Int, b: Int, c: Int }
                    invariant a >= c
                    invariant c >= b
                """, "x.a > x.b")));
    }

    @Test
    void rulesOnSiblingFieldsBelowOnePlaceTieNeitherToTheOther() {
        assertEquals(Map.of("x.a.id", RELATES), left(pair("""
                data Inner = { id: Int, owner: Int }
                data R = { a: Inner }
                    invariant a.id >= 0
                    invariant a.owner >= 0
                """, "x.a.id < x.a.owner")));
    }

    private static final String INNER = "data Inner = { id: Int, owner: Int }\n";

    @Test
    void aRuleBetweenTwoFieldsBelowOnePlaceTiesThem() {
        assertEquals(Map.of("x.a.id", NOT_READ, "x.a.owner", NOT_READ), left(pair(INNER + """
                data R = { a: Inner }
                    invariant a.id >= a.owner
                """, "x.a.id > x.a.owner")));
    }

    @Test
    void twoRulesMeetingAtAFieldBelowOnePlaceTieTheOtherTwo() {
        assertEquals(Map.of("x.a.id", NOT_READ, "x.a.owner", NOT_READ), left(pair("""
                data Inner = { id: Int, owner: Int, mid: Int }
                data R = { a: Inner }
                    invariant a.id >= a.mid
                    invariant a.mid >= a.owner
                """, "x.a.id > x.a.owner")));
    }

    private static final String SHARED = """
            data Pair = { a: Int, b: Int }
            data A = { ...Pair, left: Int }%s
            data B = { ...Pair, right: Int }%s
            data R = A | B
            """;

    /** A name the cases share stands under each of them, and the rule of a case is a rule around
     *  it. */
    @Test
    void aRuleOfEachCaseOnFieldsTheyShareTiesThem() {
        assertEquals(Map.of("x.a", NOT_READ, "x.b", NOT_READ), left(pair(SHARED.formatted(
                "\n    invariant a >= b", "\n    invariant a >= b"), "x.a > x.b")));
    }

    /** A row holds one case, so a rule of either is one the shared fields may meet. */
    @Test
    void aRuleOfOneCaseOnFieldsTheyShareTiesThemForThatCase() {
        assertEquals(Map.of("x.a", NOT_READ, "x.b", NOT_READ), left(pair(SHARED.formatted(
                "\n    invariant a >= b", ""), "x.a > x.b")));
    }

    private static final String WRAPPED = """
            data Contact = { id: Int, owner: Int }
            data Wrapped = Contact
            """;

    @Test
    void aRuleOfDistinctnessByAnotherFieldTiesNeitherOfTheTwo() {
        assertEquals(Map.of("b[*].owner", RELATES, "k", RELATES), left(elements(WRAPPED,
                "List.allDistinctBy(c -> c.value.id, value)", "c.value.owner == k")));
    }

    @Test
    void aRuleOfDistinctnessByTheFieldComparedTiesIt() {
        assertEquals(Map.of("b[*].id", RELATES, "k", NOT_READ), left(elements(WRAPPED,
                "List.allDistinctBy(c -> c.value.id, value)", "c.value.id == k")));
    }

    @Test
    void aRuleOfDistinctnessByTheWholeElementTiesThem() {
        assertEquals(Map.of("b[*].owner", RELATES, "k", NOT_READ), left(elements(WRAPPED,
                "List.allDistinctBy(c -> c, value)", "c.value.owner == k")));
    }
}
