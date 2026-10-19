package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two numbers under one input are tied by the declarations only where a rule of a value around
 * both reads something of each. A rule that reads other fields of what it sits in ties neither.
 */
class ARuleTiesOnlyThePlacesItReadsTest {

    /** Whether the report says the one comparison in {@code source} was not worked out. */
    private static boolean notRead(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .anyMatch(line -> line.strip().startsWith("· not read")
                        && line.contains("comparison@"));
    }

    private static String pair(String recordRule) {
        return """
                module w1
                data W = { v: Int }
                    invariant v >= 0
                data R = { a: W, b: W }
                    %s
                data Ans = Yes | No
                behavior m : (x: R) -> Ans
                let m (x) = if x.a.v < x.b.v then Yes else No
                """.formatted(recordRule);
    }

    private static String elements(String bookRule) {
        return """
                module w2
                data Contact = { id: Int, owner: Int }
                data Book = List<Contact>
                    invariant %s
                behavior m : (b: Book, k: Int) -> List<Contact>
                let m (b, k) = List.filter(c -> c.owner == k, b.value)
                """.formatted(bookRule);
    }

    @Test
    void aRuleOfTheTypeEachSitsInDoesNotTieTheTwo() {
        assertFalse(notRead(pair("")));
    }

    @Test
    void aRuleOfTheValueAroundBothTiesThem() {
        assertTrue(notRead(pair("invariant a.v <= b.v")));
    }

    @Test
    void aRuleOfDistinctnessByAnotherFieldOfTheElementsTiesNeitherOfTheTwo() {
        assertFalse(notRead(elements("List.allDistinctBy(c -> c.id, value)")));
    }

    @Test
    void aRuleOfDistinctnessByTheWholeElementTiesThem() {
        assertTrue(notRead(elements("List.allDistinctBy(c -> c, value)")));
    }
}
