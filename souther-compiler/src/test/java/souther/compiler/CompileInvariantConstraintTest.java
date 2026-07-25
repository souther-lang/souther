package souther.compiler;

import net.unit8.raoh.Issue;
import net.unit8.raoh.Path;
import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A newtype's invariant reaches the boundary as the Raoh constraint that says the same thing
 * (issue #83): the failure carries that constraint's code and metadata, not one
 * {@code invariant_violation} for every rule in the model. What the mapping cannot prove equivalent
 * still runs — through {@code refine}, under the shared code with the rejecting type in the metadata.
 */
class CompileInvariantConstraintTest {

    private static Issue soleIssue(String data, Object input) throws Exception {
        String module = """
                module demo

                %s
                """.formatted(data);
        ClassLoader loader = new BytesClassLoader(Compiler.compile(module), CompileInvariantConstraintTest.class.getClassLoader());
        Decoder<Object, ?> dec = Codecs.decoder(loader, "demo.V");
        Result<?> r = dec.decode(input, Path.ROOT);
        assertTrue(r instanceof Err, "the value breaks the invariant, so decoding must fail");
        List<Issue> issues = ((Err<?>) r).issues().asList();
        assertEquals(1, issues.size(), "one broken rule, one issue");
        return issues.get(0);
    }

    @Test
    void aMinimumLengthIsTooShort() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant String.length(value) > 0
                """, "");
        assertEquals("too_short", issue.code());
        assertEquals(1, issue.meta().get("min"));
        assertEquals(0, issue.meta().get("actual"));
        assertEquals("must be at least 1 characters", issue.message());
    }

    @Test
    void aMaximumLengthIsTooLong() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant String.length(value) <= 3
                """, "abcd");
        assertEquals("too_long", issue.code());
        assertEquals(3, issue.meta().get("max"));
    }

    @Test
    void anExactLengthIsAnInvalidLength() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant String.length(value) == 4
                """, "abc");
        assertEquals("invalid_length", issue.code());
    }

    @Test
    void aMatchesInvariantIsAFormat() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant String.matches("[0-9]{3}", value)
                """, "12x");
        assertEquals("invalid_format", issue.code());
    }

    @Test
    void aPositiveIntIsOutOfRange() throws Exception {
        Issue issue = soleIssue("""
                data V = Int
                    invariant value > 0
                """, 0L);
        assertEquals("out_of_range", issue.code());
        assertEquals(1L, issue.meta().get("min"));
        assertEquals(0L, issue.meta().get("actual"));
    }

    @Test
    void aNonNegativeIntIsOutOfRange() throws Exception {
        Issue issue = soleIssue("""
                data V = Int
                    invariant value >= 0
                """, -1L);
        assertEquals("out_of_range", issue.code());
        assertEquals(0L, issue.meta().get("min"));
    }

    @Test
    void anIntLowerBoundBecomesMin() throws Exception {
        Issue issue = soleIssue("""
                data V = Int
                    invariant value >= 3
                """, 2L);
        assertEquals("out_of_range", issue.code());
        assertEquals(3L, issue.meta().get("min"));
    }

    @Test
    void aStrictIntUpperBoundBecomesTheAdjacentMax() throws Exception {
        Issue issue = soleIssue("""
                data V = Int
                    invariant value < 10
                """, 10L);
        assertEquals("out_of_range", issue.code());
        assertEquals(9L, issue.meta().get("max"));
    }

    @Test
    void aMirroredBoundReadsTheSameWayRound() throws Exception {
        Issue issue = soleIssue("""
                data V = Int
                    invariant 0 <= value
                """, -5L);
        assertEquals("out_of_range", issue.code());
        assertEquals(0L, issue.meta().get("min"));
    }

    @Test
    void aDecimalLowerBoundBecomesMin() throws Exception {
        Issue issue = soleIssue("""
                data V = Decimal
                    invariant value >= 1.5m
                """, new java.math.BigDecimal("1.4"));
        assertEquals("out_of_range", issue.code());
    }

    @Test
    void anInvariantTheMappingCannotProveCarriesTheTypeName() throws Exception {
        // A quantifier over the value's characters is not a Raoh constraint; it runs as the
        // invariant it is, under the shared code, with the type that rejected the value.
        Issue issue = soleIssue("""
                data V = String
                    invariant List.all(c -> String.toCode(c) <= 57, String.toChars(value))
                """, "1a2");
        assertEquals("invariant_violation", issue.code());
        assertEquals("V", issue.meta().get("type"));
    }

    @Test
    void aMappedClauseFailsBeforeTheRestOfTheInvariantRuns() throws Exception {
        // Raoh chains constraints, so the mapped one reports on its own — the refined clause behind
        // it never sees the value, and the failure is not doubled.
        Issue issue = soleIssue("""
                data V = String
                    invariant String.length(value) > 0
                        && List.all(c -> String.toCode(c) <= 57, String.toChars(value))
                """, "");
        assertEquals("too_short", issue.code());
    }

    @Test
    void aConstrainedNewtypeStillReportsAtItsFieldsPath() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Label = String
                    invariant String.length(value) > 0

                data Board = { label: Label }
                """), getClass().getClassLoader());
        Result<?> r = Codecs.decoder(loader, "demo.Board").decode(Map.of("label", ""), Path.ROOT);
        assertTrue(r instanceof Err);
        Issue issue = ((Err<?>) r).issues().asList().get(0);
        assertEquals("too_short", issue.code());
        assertEquals(List.of("label"), issue.path().segments());
    }

    @Test
    void aValueThatHoldsStillDecodes() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = String
                    invariant String.length(value) > 0
                        && String.matches("[a-z]+", value)
                """), getClass().getClassLoader());
        Result<?> r = Codecs.decoder(loader, "demo.V").decode("ok", Path.ROOT);
        assertTrue(r instanceof Ok, "a value the invariant admits decodes as before");
    }
}
