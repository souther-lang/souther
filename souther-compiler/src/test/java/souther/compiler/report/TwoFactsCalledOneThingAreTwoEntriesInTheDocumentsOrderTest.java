package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a document writes about a model two of whose sources were not read, written out.
 *
 * <p>Two sources nothing was observed from are two facts. They are the same word about the same
 * kind of thing, and what tells them apart is which source — so one array of this document writes
 * them as two entries a reader cannot tell apart, and the other as two entries a reader can.
 *
 * <p><b>What is asked here is the wiring and not the order.</b> That an order is a total one over
 * what a document writes is asked of the order, over every sequence its members could be met in;
 * this asks that the document's arrays go through it at all, over data a compiler produced rather
 * than data a test built. A renderer that walked the account directly would answer this correctly
 * on a model whose facts are met in one order, which is every model with one such source — so the
 * model here has two.
 *
 * <p><b>And that the two arrays disagree on purpose.</b> {@code keptOpenBy} counts facts, so two
 * facts one word covers are two entries and neither is folded away. {@code incompleteness} counts
 * kinds per module and says which source each was about, so the two are told apart there. A change
 * that made either behave like the other would pass one half of this and fail the other.
 */
class TwoFactsCalledOneThingAreTwoEntriesInTheDocumentsOrderTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** One module, and two further sources of examples for it that redefine what it already has —
     *  so neither is evaluated and nothing is observed from either. */
    private static final List<String> TWO_SOURCES_NOTHING_WAS_READ_FROM = List.of("""
            module example.split

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Yes
            data No
            data Flag = Yes | No

            data Draft = { cost: Amount, flag: Flag }
            data Ok = { n: Int }
            data Refused = { why: String }

            let shared = Draft { cost = Amount(7), flag = Yes }

            behavior take : (request: Draft) -> Ok | Refused
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            example take
                | (Draft { cost = Amount(7), flag = Yes }) -> Ok { n = 7 }
            """, """
            examples for example.split

            let shared = Draft { cost = Amount(0), flag = No }

            example take
                | (Draft { cost = Amount(0), flag = No }) -> Ok { n = 0 }
            """, """
            examples for example.split

            let shared = Draft { cost = Amount(3), flag = No }

            example take
                | (Draft { cost = Amount(3), flag = No }) -> Ok { n = 3 }
            """);

    /**
     * Both, and neither folded away.
     *
     * <p>The two entries are identical, which is what the array is for: its unit is the fact, and a
     * reader counting it counts how many things hold the verdict open rather than how many words
     * this document has for them.
     */
    @Test
    void twoFactsOneWordCoversAreTwoEntriesOfThatWord() {
        assertEquals("""
                [ {
                  "kind" : "observation_absent",
                  "runSensitivity" : "unaffected"
                }, {
                  "kind" : "observation_absent",
                  "runSensitivity" : "unaffected"
                } ]""",
                written().get("keptOpenBy").toPrettyString());
    }

    /**
     * And the same two, told apart by what each was about, in the order this document says them in.
     *
     * <p>Which source came first is not the order they were met in but the order the identities are
     * compared in, which is what a run comparing this document against the last one needs.
     */
    @Test
    void theSameTwoAreToldApartByWhichSourceAndArrangedByIt() {
        assertEquals("""
                [ {
                  "code" : "observation_absent",
                  "scope" : "source",
                  "subject" : "1"
                }, {
                  "code" : "observation_absent",
                  "scope" : "source",
                  "subject" : "2"
                } ]""",
                written().get("modules").get(0).get("incompleteness").toPrettyString());
    }

    /**
     * And the table of sources this document owes an explanation of follows from writing them.
     *
     * <p>Not an order of its own. A source is recorded as the document writes its identity, so the
     * table comes out in the order the entries above did — which is a consequence of those being
     * arranged before anything was written, and would be the order a comparison happened to ask
     * about them in if a place were chosen while writing.
     */
    @Test
    void theSourcesThisDocumentExplainsFollowFromWritingThem() {
        assertEquals("""
                {
                  "1" : "1",
                  "2" : "2"
                }""", written().get("sources").toPrettyString());
    }

    private static JsonNode written() {
        Compilation compilation =
                Compilation.ofSources(TWO_SOURCES_NOTHING_WAS_READ_FROM, ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(
                AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
    }
}
