package souther.compiler;

import souther.compiler.jvm.DecoderKind;
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
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
        // Raoh's own message, not one minted here, so a resolver may replace it
        assertFalse(issue.customMessage(), "the message must stay replaceable");
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
                    invariant List.all(c -> c <= 57, String.codePoints(value))
                """, "1a2");
        assertEquals("invariant_violation", issue.code());
        assertEquals("V", issue.meta().get("type"));
        // the same replaceability the mapped constraints have: refine's message overload would mint a
        // custom-message issue that a resolver refuses to touch, so the failure is built by hand
        assertFalse(issue.customMessage(), "an invariant's text must stay replaceable");
        assertEquals("resolved", issue.resolve((code, meta) -> "resolved").message());
    }

    @Test
    void aMappedClauseFailsBeforeTheRestOfTheInvariantRuns() throws Exception {
        // Raoh chains constraints, so the mapped one reports on its own — the refined clause behind
        // it never sees the value, and the failure is not doubled.
        Issue issue = soleIssue("""
                data V = String
                    invariant String.length(value) > 0
                        && List.all(c -> c <= 57, String.codePoints(value))
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
    void aPatternIsCompiledOncePerDecoderNotPerDecode() throws Exception {
        // The constraint chain is rebuilt on every decode call, so a regex compiled there would be
        // recompiled per value; it is held in a static field of the decoder instead.
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data V = String
                    invariant String.matches("[0-9]{3}", value)
                """), getClass().getClassLoader());
        Class<?> dec = loader.loadClass(Emitted.decoder("demo", "V", DecoderKind.VALUE));
        long patterns = java.util.Arrays.stream(dec.getDeclaredFields())
                .filter(f -> f.getType() == java.util.regex.Pattern.class)
                .filter(f -> java.lang.reflect.Modifier.isStatic(f.getModifiers()))
                .count();
        assertEquals(1, patterns, "the invariant's regex is a static field of the decoder");
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

    // --- collections ---

    @Test
    void anEmptyListIsTooSmall() throws Exception {
        Issue issue = soleIssue("""
                data V = List<Int>
                    invariant List.length(value) >= 1
                """, List.of());
        assertEquals("too_small", issue.code(), "Raoh states emptiness itself");
        assertEquals(1, issue.meta().get("min"));
        assertEquals(0, issue.meta().get("actual"));
        assertFalse(issue.customMessage(), "the message is Raoh's, so a resolver may replace it");
    }

    @Test
    void aListShorterThanItsMinimumIsTooSmall() throws Exception {
        Issue issue = soleIssue("""
                data V = List<Int>
                    invariant List.length(value) >= 3
                """, List.of(1L, 2L));
        assertEquals("too_small", issue.code());
        assertEquals(3, issue.meta().get("min"));
        assertEquals(2, issue.meta().get("actual"));
    }

    @Test
    void aListLongerThanItsMaximumIsTooBig() throws Exception {
        Issue issue = soleIssue("""
                data V = List<Int>
                    invariant List.length(value) <= 1
                """, List.of(1L, 2L));
        assertEquals("too_big", issue.code());
        assertEquals(1, issue.meta().get("max"));
    }

    /** {@code allDistinctBy} with the identity projection says of the elements what Raoh's
     * {@code unique()} says of them, and Raoh names the duplicates it found. */
    @Test
    void aRepeatedElementIsADuplicate() throws Exception {
        Issue issue = soleIssue("""
                data V = List<Int>
                    invariant List.allDistinctBy(x -> x, value)
                """, List.of(1L, 2L, 1L));
        assertEquals("duplicate_element", issue.code());
        assertEquals(List.of(1L), issue.meta().get("duplicates"));
    }

    /** A projection that is not the identity says it of something else, and Raoh has no constraint for
     * that: the clause keeps its own check, and names itself in the metadata instead. */
    @Test
    void aProjectedUniquenessKeepsItsOwnCheck() throws Exception {
        Issue issue = soleIssue("""
                data Line = { product: String, qty: Int }
                data V = List<Line>
                    invariant uniqueProducts = List.allDistinctBy(.product, value)
                """, List.of(Map.of("product", "a", "qty", 1L), Map.of("product", "a", "qty", 2L)));
        assertEquals("invariant_violation", issue.code());
        assertEquals("V", issue.meta().get("type"));
        assertEquals("uniqueProducts", issue.meta().get("clause"));
        assertFalse(issue.customMessage(), "an invariant's text must stay replaceable");
    }

    @Test
    void aMapWithTooFewEntriesIsTooSmall() throws Exception {
        Issue issue = soleIssue("""
                data V = Map<String, Int>
                    invariant Map.size(value) >= 2
                """, Map.of("a", 1L));
        assertEquals("too_small", issue.code());
        assertEquals(2, issue.meta().get("min"));
    }

    // --- what a clause's name adds ---

    /** A clause no constraint states carries its name, so a boundary failure says which rule broke
     * rather than only that the value was rejected. */
    @Test
    void aNamedClauseNamesItselfInTheMetadata() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant digitsOnly = List.all(c -> c <= 57, String.codePoints(value))
                """, "1a2");
        assertEquals("invariant_violation", issue.code());
        assertEquals("V", issue.meta().get("type"));
        assertEquals("digitsOnly", issue.meta().get("clause"));
    }

    /** A clause declared without a name has nothing to be told apart by, and says so by carrying no
     * clause in the metadata — the type still travels. */
    @Test
    void anUnnamedClauseCarriesOnlyTheType() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant List.all(c -> c <= 57, String.codePoints(value))
                """, "1a2");
        assertEquals("V", issue.meta().get("type"));
        assertNull(issue.meta().get("clause"), "there is no name to report");
    }

    /**
     * What a type is, is its module and its name, so the metadata carries both: two modules may each
     * declare an `Id`, and a resolver keyed on the simple name alone would answer for either.
     */
    @Test
    void theRejectingTypeIsNamedByItsModuleToo() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module sales exposing ( Id )
                data Id = String
                    invariant shaped = List.all(c -> c <= 57, String.codePoints(value))
                """, """
                module customer exposing ( Id )
                data Id = String
                    invariant shaped = List.all(c -> c <= 57, String.codePoints(value))
                """)), getClass().getClassLoader());

        Issue sales = sole(Codecs.decoder(loader, "sales.Id").decode("x", Path.ROOT));
        Issue customer = sole(Codecs.decoder(loader, "customer.Id").decode("x", Path.ROOT));
        assertEquals("sales", sales.meta().get("module"));
        assertEquals("customer", customer.meta().get("module"));
        assertEquals("Id", sales.meta().get("type"), "the name stays the name");
        assertEquals("Id", customer.meta().get("type"));
        assertTrue(sales.message().contains("sales.Id"),
                "and the default message names the type as Souther identifies it: " + sales.message());
    }

    private static Issue sole(Result<?> r) {
        assertTrue(r instanceof Err, "the value breaks the invariant, so decoding must fail");
        List<Issue> issues = ((Err<?>) r).issues().asList();
        assertEquals(1, issues.size(), "one broken rule, one issue");
        return issues.get(0);
    }

    /**
     * The order a failure is reported in is the order the clauses are declared in, which is the order
     * {@code __construct} decides in too — so the boundary and an attempted construction name the same
     * clause for the same value. A mapped clause written after an unmapped one gives up Raoh's code to
     * keep that: Raoh's typed constraints cannot be chained behind a {@code refine}.
     */
    @Test
    void anEarlierClauseIsReportedThoughALaterOneMapsOntoAConstraint() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant digitsOnly = List.all(c -> c <= 57, String.codePoints(value))
                    invariant long = String.length(value) >= 5
                """, "1a2");
        assertEquals("invariant_violation", issue.code(), "the first failing clause is the refined one");
        assertEquals("digitsOnly", issue.meta().get("clause"));
    }

    @Test
    void aMappedClauseDeclaredFirstKeepsItsCode() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant long = String.length(value) >= 5
                    invariant digitsOnly = List.all(c -> c <= 57, String.codePoints(value))
                """, "1a2");
        assertEquals("too_short", issue.code());
    }

    /** A product data's invariant has no single value for a constraint to be about, so it is checked
     * where the value is built — and that failure now says which rule it was. */
    @Test
    void aProductDataReportsTheClauseThatFailed() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Span = { from: Int, to: Int }
                    invariant ordered = from <= to
                """), getClass().getClassLoader());
        Result<?> r = Codecs.decoder(loader, "demo.Span")
                .decode(Map.of("from", 5L, "to", 1L), Path.ROOT);
        assertTrue(r instanceof Err);
        Issue issue = ((Err<?>) r).issues().asList().get(0);
        assertEquals("invariant_violation", issue.code());
        assertEquals("demo", issue.meta().get("module"), "which module declared the type");
        assertEquals("Span", issue.meta().get("type"), "which type rejected the value");
        assertEquals("ordered", issue.meta().get("clause"));
        assertFalse(issue.customMessage());
    }

    /**
     * The boundary and the domain count a length the same way. {@code String.length} counts Unicode
     * code points, and the derived decoder hands the bound to Raoh, which counts them too — so a
     * name written with a supplementary-plane kanji gets one answer, not two. Counting UTF-16 units
     * at the boundary would reject a value the model accepts, and the caller would see the boundary's
     * answer.
     */
    @Test
    void aLengthBoundMeansTheSameAtTheBoundaryAsInTheModel() throws Exception {
        String data = """
                data V = String
                    invariant String.length(value) <= 2
                """;
        ClassLoader loader = new BytesClassLoader(Compiler.compile("module demo\n\n" + data),
                getClass().getClassLoader());
        Decoder<Object, ?> dec = Codecs.decoder(loader, "demo.V");

        // 𠮷田: two characters, four UTF-16 units. The model admits it, so the decoder must too.
        assertTrue(dec.decode("𠮷田", Path.ROOT) instanceof Ok,
                "a two-code-point value inside a bound of 2 must decode");

        Issue issue = soleIssue(data, "𠮷田山");   // 𠮷田山: three characters
        assertEquals("too_long", issue.code());
        assertEquals(3, issue.meta().get("actual"), "the reported length is in code points");
    }
}
