package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule written under a container is read where it governs, and the position above it is short of
 * nothing for it.
 *
 * <p>What a declaration states is stated about values of that declaration. An optional holds one or
 * holds none, a sum is one of its cases, a sequence holds however many — and in none of those is the
 * rule of the thing held a rule about every value standing at the position above. So the reading of
 * that rule belongs one position down, where a row meets it and a border is owed against it, and the
 * position above has read everything that was ever addressed to it.
 *
 * <p>Read the other way, the position above reported a rule it never reached and no row could
 * discharge it: the walk had gone to the rule, one position down, and the accounting was working out
 * for itself that a rule stood somewhere under the type. A measure short of something nobody can
 * supply is short for good (#1072).
 *
 * <p><b>Three shapes and one claim.</b> The claim is about where a rule is read and not about
 * containers, so it is written against each shape this compiler descends through rather than against
 * the one the defect was found on. What each of them asserts is the same two things: the position
 * below carries the classes the rule draws, and the measure is weakened by nothing.
 */
class RulesUnderAContainerAreReachedWhereTheyGovernTest {

    /** A rule that names values, so that reaching it is visible as classes and not only as a word
     *  about how far a reading got. */
    private static final String TAG = """
                data Tag = String
                    invariant named = value == "a" || value == "b"
            """;

    private static final String OPTIONAL = """
            module example.optional
            """ + TAG + """
            data Query = { tag: Tag?, other: Int }
            data Page = { count: Int }

            behavior read : (query: Query) -> Page
                constructs Page
            let read (query) = Page { count = 0 }

            example read
                | "with"    : (Query { tag = Tag("a"), other = 0 }) -> Page { count = 0 }
                | "without" : (Query { other = 0 }) -> Page { count = 0 }
            """;

    private static final String SUM = """
            module example.sum
            """ + TAG + """
            data NoTag
            data Filter = Tag | NoTag
            data Query = { tag: Filter, other: Int }
            data Page = { count: Int }

            behavior read : (query: Query) -> Page
                constructs Page
            let read (query) = Page { count = 0 }

            example read
                | "tagged"   : (Query { tag = Tag("a"), other = 0 }) -> Page { count = 0 }
                | "untagged" : (Query { tag = NoTag, other = 0 }) -> Page { count = 0 }
            """;

    private static final String SEQUENCE = """
            module example.sequence
            """ + TAG + """
            data Query = { tags: List<Tag>, other: Int }
            data Page = { count: Int }

            behavior read : (query: Query) -> Page
                constructs Page
            let read (query) = Page { count = 0 }

            example read
                | "one" : (Query { tags = [ Tag("a") ], other = 0 }) -> Page { count = 0 }
            """;

    /**
     * What an optional holds is read at the narrowing that says it holds something.
     *
     * <p>And the optional itself divides into the two ways it can turn out, with every rule ever
     * addressed to it read: there is no clause about a value that may not be there.
     */
    @Test
    void aRuleBehindAnOptionalIsReadAtTheNarrowing() {
        PartitionEvidence read = evidenceFor(OPTIONAL);

        assertEquals(List.of("\"a\"", "\"b\""), classesAt(read, "query.tag@Some"),
                "the rule of the type behind the `?` draws the classes at the narrowing");
        assertReadToTheEnd(read, "query.tag");
        assertReadToTheEnd(read, "query.tag@Some");
        assertNothingIsOutOfSight(read);
    }

    /** A rule on one case of a sum is read at that case. */
    @Test
    void aRuleOnOneCaseOfASumIsReadAtTheCase() {
        PartitionEvidence read = evidenceFor(SUM);

        assertEquals(List.of("\"a\"", "\"b\""), classesAt(read, "query.tag@Tag"),
                "the case's own rule draws the classes at the case");
        assertReadToTheEnd(read, "query.tag");
        assertReadToTheEnd(read, "query.tag@Tag");
        assertNothingIsOutOfSight(read);
    }

    /**
     * And a rule on what a sequence holds is read at the element.
     *
     * <p>The element is a value with a declaration of its own, exactly as what stands under a
     * narrowing is. Read as the sequence's own business, the rule reached no position at all: the
     * model divided nowhere and the report named two positions it had not read, one of them the
     * element the border was nevertheless owed at.
     */
    @Test
    void aRuleOnWhatASequenceHoldsIsReadAtTheElement() {
        PartitionEvidence read = evidenceFor(SEQUENCE);

        assertEquals(List.of("\"a\"", "\"b\""), classesAt(read, "query.tags[*]"),
                "the element's own rule draws the classes at the element");
        // And not at the sequence itself, which has no axis: nothing bounds how many it holds, so
        // the model divides it nowhere. What is asserted of it is that nothing is out of sight
        // there, which is the line below.
        assertReadToTheEnd(read, "query.tags[*]");
        assertNothingIsOutOfSight(read);
    }

    /** The classes the model divides one position into, in the order the reading answers them. */
    private static List<String> classesAt(PartitionEvidence read, String path) {
        return List.copyOf(axisAt(read, path).classes());
    }

    /** That the reading at one position was short of no rule, which is what no row can supply. */
    private static void assertReadToTheEnd(PartitionEvidence read, String path) {
        assertEquals(PartitionEvidence.AxisCoverage.Reach.EVERY_RULE, axisAt(read, path).read().reach(),
                () -> "how far the rules at " + path + " were read");
    }

    private static PartitionEvidence.AxisCoverage axisAt(PartitionEvidence read, String path) {
        PartitionEvidence.AxisCoverage found = read.axes().stream()
                .filter(each -> each.path().equals(path)).findFirst().orElse(null);
        assertNotNull(found, () -> path + " is not among "
                + read.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList());
        return found;
    }

    /**
     * And that the measure as a whole is weakened by nothing.
     *
     * <p>Beside the positions rather than instead of them. A position asserted read to the end says
     * nothing about a second position the same walk gave up on, and what an author is told is that
     * the measure is partial — so the claim these models make is that there is no such position
     * anywhere in them.
     */
    private static void assertNothingIsOutOfSight(PartitionEvidence read) {
        assertTrue(read.weakening().isEmpty(),
                () -> "the measure is weakened by " + read.weakening());
        assertEquals(List.of(), read.notRead(),
                () -> "and nothing was left unread");
    }

    private static PartitionEvidence evidenceFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return partitions.get("read");
    }
}
