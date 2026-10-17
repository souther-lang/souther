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
 * A comparison against a field of a list's element, or a field the cases of a sum share, is read
 * as the same comparison against a field of one product: where nothing holds either side back,
 * each reaches the other, and where something does, it still does not.
 *
 * <p>An element is reached only where the list holds one, so the rows that arrive at a comparison
 * inside {@code List.filter} are ones whose list is not empty; that says nothing of what the
 * element is. A shared field stands under each case, and a row holds one of them; it takes what
 * every case leaves it where they leave it the same.
 */
class AComparisonAgainstAPlaceUnderAListOrASumReachesAsOneUnderAProductTest {

    private static final String RELATES = "relates";

    private static final String NOT_SHOWN = "not shown";

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
            out.put(place, line.contains("rather than dividing the values here") ? RELATES
                    : line.contains("not shown to reach every value here") ? NOT_SHOWN : line);
        }
        return out;
    }

    private static final String SUM = """
            module sumfield
            data Ok
            data Bad
            data Base = { n: Int, d: Date }
            data A = { ...Base, a: Int }
            data B = { ...Base, b: Int }%s
            data S = A | B
            behavior sum : (s: S, t: Date) -> Ok | Bad
            let sum (s, t) = {
                guard Date.daysBetween(t, s.d) >= 0 else Bad
                Ok
            }
            """;

    @Test
    void aFieldOfOneProduct() {
        assertEquals(Map.of("a.owner", RELATES, "owner", RELATES), left("""
                module v1
                data Meeting = { owner: Int, m: Int }
                behavior one : (a: Meeting, owner: Int) -> Int
                let one (a, owner) = if a.owner == owner then 1 else 0
                """));
    }

    @Test
    void aFieldOfAListsElement() {
        assertEquals(Map.of("a[*].owner", RELATES, "owner", RELATES), left("""
                module v2
                data Meeting = { owner: Int, m: Int }
                behavior many : (a: List<Meeting>, owner: Int) -> List<Meeting>
                let many (a, owner) = List.filter(m -> m.owner == owner, a)
                """));
    }

    /** A rule of the element's field holds it to a run, which a plain number runs past. */
    @Test
    void aFieldOfAListsElementARuleHoldsReachesNoMoreThanTheRule() {
        assertEquals(Map.of("a[*].owner", RELATES, "owner", NOT_SHOWN), left("""
                module v2
                data Owner = Int invariant value >= 0
                data Meeting = { owner: Owner, m: Int }
                behavior many : (a: List<Meeting>, owner: Int) -> List<Meeting>
                let many (a, owner) = List.filter(m -> m.owner.value == owner, a)
                """));
    }

    /**
     * A rule of the element relating the field compared to a field it leaves free leaves the
     * field every value; once that field is held to ten, so is the one compared, and an owner of
     * eleven is in no element.
     */
    @Test
    void aFieldOfAListsElementWhoseRuleRelatesItToAnotherReachesWhatTheRuleLeavesIt() {
        assertEquals(Map.of("a[*].owner", RELATES, "owner", RELATES), left("""
                module v2
                data Meeting = { owner: Int, m: Int } invariant owner <= m
                behavior many : (a: List<Meeting>, owner: Int) -> List<Meeting>
                let many (a, owner) = List.filter(m -> m.owner == owner, a)
                """));
        assertEquals(Map.of("a[*].owner", RELATES, "owner", NOT_SHOWN), left("""
                module v2
                data Meeting = { owner: Int, m: Int } invariant owner <= m && m <= 10
                behavior many : (a: List<Meeting>, owner: Int) -> List<Meeting>
                let many (a, owner) = List.filter(m -> m.owner == owner, a)
                """));
    }

    @Test
    void aFieldTheCasesOfASumShare() {
        assertEquals(Map.of("s.d", RELATES, "t", RELATES), left(SUM.formatted("")));
    }

    /** What one case leaves the field is not what it takes in a row of the other. */
    @Test
    void aFieldTheCasesOfASumShareWhereOneCaseHoldsItBackIsNotShown() {
        assertEquals(Map.of("s.d", RELATES, "t", NOT_SHOWN), left(SUM.formatted(
                " invariant Date.year(d) >= 2000")));
    }

    @Test
    void aFieldOfACaseMatchedInAListsElement() {
        assertEquals(Map.of("a[*]@Meeting.owner", RELATES, "owner", RELATES), left("""
                module v3
                data Task = { owner: Int }
                data Meeting = { owner: Int }
                data Act = Task | Meeting
                behavior many : (a: List<Act>, owner: Int) -> List<Act>
                let many (a, owner) = List.filter(x -> match x with
                    | Meeting as m -> m.owner == owner
                    | Task -> false, a)
                """));
    }
}
