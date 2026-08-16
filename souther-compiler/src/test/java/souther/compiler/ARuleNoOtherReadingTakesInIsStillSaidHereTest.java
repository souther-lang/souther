package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule stating an end past the end of an order, said by whichever reading is its only one.
 *
 * <p>Such a rule is read: what it says is that nothing satisfies it. Where the declaration is
 * refused for that, this report is never produced, and naming the rule here as one nothing could
 * read would send an author after a bound the compiler understood perfectly.
 *
 * <p>Where nothing refuses it, this report is its only reader. A size is that case: the reading that
 * refuses a declaration for holding no value is over the positions a value has, and a size is a
 * number taken of one, so no end of a size reaches it. Silence here would leave the rule unsaid
 * everywhere — which is what a reading justified by "something else refuses this" costs when the
 * justification is borrowed by a caller it is not true of.
 */
class ARuleNoOtherReadingTakesInIsStillSaidHereTest {

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    /** A size bounded past the greatest whole number, which nothing else takes in. */
    @Test
    void aSizeBoundPastTheEndOfTheWholeNumbersIsNamedAsUnread() {
        String human = reportOf("""
                module example.sized

                data Tag = String
                    invariant long = String.length(value) > 9223372036854775807

                data Short
                data Long

                behavior weigh : (t: Tag) -> Short | Long
                    constructs Short, Long
                let weigh (t) = if String.length(t.value) > 3 then Long else Short
                """);

        assertTrue(human.contains("not read: t"), human);
    }

    /**
     * And an ordinary size bound is read, so nothing is said about it.
     *
     * <p>The control. Without it the assertion above holds of a reading that calls every size rule
     * unread, which is the answer this is meant to tell apart.
     */
    @Test
    void anOrdinarySizeBoundIsNotNamedAsUnread() {
        String human = reportOf("""
                module example.sized

                data Tag = String
                    invariant long = String.length(value) > 2

                data Short
                data Long

                behavior weigh : (t: Tag) -> Short | Long
                    constructs Short, Long
                let weigh (t) = if String.length(t.value) > 3 then Long else Short
                """);

        assertFalse(human.contains("not read: t"), human);
    }
}
