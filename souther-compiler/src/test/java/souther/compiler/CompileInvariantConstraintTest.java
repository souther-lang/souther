package souther.compiler;

import souther.compiler.core.BoundaryConstraint;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.DecoderKind;
import souther.runtime.ConstraintViolation;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Path;
import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import net.unit8.raoh.decode.ObjectDecoders;
import net.unit8.raoh.decode.builtin.ListDecoder;
import net.unit8.raoh.decode.builtin.RecordDecoder;
import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ConstantDynamicEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.constant.ClassDesc;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A newtype's invariant reaches the boundary as the Raoh constraint that says the same thing: the
 * failure carries that constraint's code and metadata, not one {@code invariant_violation} for every
 * rule in the model. What the mapping cannot prove equivalent still runs — through {@code refine},
 * under the shared code with the rejecting type in the metadata.
 *
 * <p>Where Raoh states a constraint, the claim is that the issue is the one Raoh builds for it, field
 * for field, so the codes and metadata are asked of Raoh and not written here a second time.
 */
class CompileInvariantConstraintTest {

    private static Decoder<Object, ?> decoderOf(String data) throws Exception {
        String module = """
                module demo

                %s
                """.formatted(data);
        ClassLoader loader = new BytesClassLoader(Compiler.compile(module), CompileInvariantConstraintTest.class.getClassLoader());
        return Codecs.decoder(loader, "demo.V");
    }

    private static Issue soleIssue(String data, Object input) throws Exception {
        return sole(decoded(data, input));
    }

    private static Result<?> decoded(String data, Object input) throws Exception {
        return decoderOf(data).decode(input, Path.ROOT);
    }

    private static Issue firstIssue(Result<?> r) {
        assertTrue(r instanceof Err, "the value breaks the invariant, so decoding must fail");
        return ((Err<?>) r).issues().asList().get(0);
    }

    private static Optional<Issue> issueOf(Decoder<Object, ?> decoder, Object input) {
        return decoder.decode(input, Path.ROOT) instanceof Err<?> err
                ? Optional.of(err.issues().asList().get(0))
                : Optional.empty();
    }

    private static Issue sole(Result<?> r) {
        assertTrue(r instanceof Err, "the value breaks the invariant, so decoding must fail");
        List<Issue> issues = ((Err<?>) r).issues().asList();
        assertEquals(1, issues.size(), "one broken rule, one issue");
        return issues.get(0);
    }

    private static ListDecoder<Object, Object> raohList(List<?> elements) {
        List<Object> held = new ArrayList<>(elements);
        return new ListDecoder<>((in, path) -> Result.ok(held));
    }

    private static RecordDecoder<Object, Object> raohMap(Map<String, Object> entries) {
        return new RecordDecoder<>((in, path) -> Result.ok(entries));
    }

    private record Mapped(String type, String clause, Object input, Supplier<Result<?>> raoh) {
    }

    /**
     * A clause the mapping states is reported as the constraint Raoh states for it. Each row is a
     * clause, the value that breaks it, and the constraint Raoh would have been asked for the same
     * thing; an adjusted bound ({@code < 10} is a maximum of 9) is the row that says how.
     */
    @Test
    void aClauseTheMappingStatesIsReportedAsTheIssueRaohBuildsForIt() throws Exception {
        Map<String, Object> oneEntry = Map.of("a", 1L);
        List<Mapped> rows = List.of(
                new Mapped("String", "String.length(value) > 0", "",
                        () -> ObjectDecoders.string().minLength(1).decode("", Path.ROOT)),
                new Mapped("String", "String.length(value) <= 3", "abcd",
                        () -> ObjectDecoders.string().maxLength(3).decode("abcd", Path.ROOT)),
                new Mapped("String", "String.length(value) == 4", "abc",
                        () -> ObjectDecoders.string().fixedLength(4).decode("abc", Path.ROOT)),
                new Mapped("String", "String.matches(\"[0-9]{3}\", value)", "12x",
                        () -> ObjectDecoders.string().pattern("[0-9]{3}").decode("12x", Path.ROOT)),
                new Mapped("Int", "value > 0", 0L,
                        () -> ObjectDecoders.long_().positive().decode(0L, Path.ROOT)),
                new Mapped("Int", "value >= 0", -1L,
                        () -> ObjectDecoders.long_().nonNegative().decode(-1L, Path.ROOT)),
                new Mapped("Int", "value >= 3", 2L,
                        () -> ObjectDecoders.long_().min(3).decode(2L, Path.ROOT)),
                new Mapped("Int", "value < 10", 10L,
                        () -> ObjectDecoders.long_().max(9).decode(10L, Path.ROOT)),
                new Mapped("Int", "0 <= value", -5L,
                        () -> ObjectDecoders.long_().nonNegative().decode(-5L, Path.ROOT)),
                new Mapped("Decimal", "value >= 1.5m", new BigDecimal("1.4"),
                        () -> ObjectDecoders.decimal().min(new BigDecimal("1.5"))
                                .decode(new BigDecimal("1.4"), Path.ROOT)),
                new Mapped("List<Int>", "List.length(value) >= 1", List.of(),
                        () -> raohList(List.of()).nonempty().decode(List.of(), Path.ROOT)),
                new Mapped("List<Int>", "List.length(value) >= 3", List.of(1L, 2L),
                        () -> raohList(List.of(1L, 2L)).minSize(3).decode(List.of(1L, 2L), Path.ROOT)),
                new Mapped("List<Int>", "List.length(value) <= 1", List.of(1L, 2L),
                        () -> raohList(List.of(1L, 2L)).maxSize(1).decode(List.of(1L, 2L), Path.ROOT)),
                new Mapped("List<Int>", "List.length(value) == 1", List.of(1L, 2L),
                        () -> raohList(List.of(1L, 2L)).fixedSize(1).decode(List.of(1L, 2L), Path.ROOT)),
                new Mapped("Map<String, Int>", "Map.size(value) >= 2", oneEntry,
                        () -> raohMap(oneEntry).minSize(2).decode(oneEntry, Path.ROOT)),
                new Mapped("Map<String, Int>", "Map.size(value) < 1", oneEntry,
                        () -> raohMap(oneEntry).maxSize(0).decode(oneEntry, Path.ROOT)),
                new Mapped("Map<String, Int>", "Map.size(value) >= 1", Map.of(),
                        () -> raohMap(Map.of()).nonempty().decode(Map.of(), Path.ROOT)),
                new Mapped("List<Int>", "List.allDistinctBy(x -> x, value)", List.of(1L, 2L, 1L),
                        () -> raohList(List.of(1L, 2L, 1L)).unique().decode(List.of(1L, 2L, 1L), Path.ROOT)));
        for (Mapped row : rows) {
            Issue issue = soleIssue("data V = %s\n    invariant %s\n".formatted(row.type(), row.clause()),
                    row.input());
            assertEquals(sole(row.raoh().get()), issue, row.clause());
            assertFalse(issue.customMessage(), row.clause() + ": the message stays replaceable");
        }
    }

    private record Wrapped(String declarations, Object input) {
    }

    /**
     * A uniqueness over elements Raoh can compare says what Raoh's own {@code unique()} says of the
     * boundary form of the same elements: a newtype is reported as the value it wraps, through every
     * name it wears and inside every list it stands in.
     */
    @Test
    void aRepeatedElementIsReportedAsRaohReportsTheValueItWraps() throws Exception {
        List<Wrapped> rows = List.of(
                new Wrapped("data Sku = String\ndata V = List<Sku>", List.of("A123", "B456", "A123")),
                new Wrapped("data Code = Int\ndata Sku = Code\ndata V = List<List<Sku>>",
                        List.of(List.of(1L, 2L), List.of(3L), List.of(1L, 2L))),
                new Wrapped("data Skus = List<String>\ndata V = List<Skus>",
                        List.of(List.of("a"), List.of("a"))));
        for (Wrapped row : rows) {
            Issue issue = soleIssue(row.declarations() + "\n    invariant List.allDistinctBy(x -> x, value)\n",
                    row.input());
            assertEquals(sole(raohList((List<?>) row.input()).unique().decode(row.input(), Path.ROOT)),
                    issue, row.declarations());
        }
    }

    /**
     * {@code Unique} is stated of the elements' Souther equality, and two spellings of one amount are
     * one element by it — where Raoh's own {@code unique()} would tell them apart by
     * {@code BigDecimal.equals}, which reads the scale. Each repeated element is named once, at the
     * point its repetition is first found: not at its own first occurrence, and not again once it has
     * been named.
     */
    @Test
    void aDecimalRepeatedAtAnotherScaleIsADuplicate() throws Exception {
        record Row(String type, List<Object> input, List<Object> duplicates) {
        }
        List<Row> rows = List.of(
                new Row("List<Decimal>", List.of(new BigDecimal("1.0"), new BigDecimal("1.00")),
                        List.of(new BigDecimal("1.00"))),
                new Row("List<List<Decimal>>",
                        List.of(List.of(new BigDecimal("1.0")), List.of(new BigDecimal("1.00"))),
                        List.of(List.of(new BigDecimal("1.00")))),
                new Row("List<Decimal>",
                        List.of(new BigDecimal("1.0"), new BigDecimal("2.0"), new BigDecimal("2.00"),
                                new BigDecimal("1.00"), new BigDecimal("1.000")),
                        List.of(new BigDecimal("2.00"), new BigDecimal("1.00"))));
        for (Row row : rows) {
            Issue issue = soleIssue("data V = %s\n    invariant List.allDistinctBy(x -> x, value)\n"
                    .formatted(row.type()), row.input());
            assertEquals("duplicate_element", issue.code(), row.type());
            assertEquals(row.duplicates(), issue.meta().get("duplicates"), row.type());
            assertFalse(issue.customMessage(), "Raoh's own message, so a resolver may replace it");
        }
    }

    private record OwnCheck(String declarations, String clause, Object input) {
    }

    /**
     * What has no message form — a product, a map, a newtype over a product, a newtype that holds
     * itself through a list, a projection that is not the identity, a clause no constraint states —
     * keeps its own check, and names itself in the metadata instead: the type that rejected the value
     * and the clause, if it has a name.
     */
    @Test
    void aClauseWithNoConstraintForItKeepsItsOwnCheck() throws Exception {
        List<Object> lines = List.of(Map.of("sku", "a"), Map.of("sku", "a"));
        List<OwnCheck> rows = List.of(
                new OwnCheck("data Line = { sku: String }\ndata V = List<Line>", "distinctLines = List.allDistinctBy(x -> x, value)", lines),
                new OwnCheck("data V = List<Map<String, Int>>", "distinctTallies = List.allDistinctBy(x -> x, value)",
                        List.of(Map.of("a", 1L), Map.of("a", 1L))),
                new OwnCheck("data Line = { sku: String }\ndata Entry = Line\ndata V = List<Entry>",
                        "distinctEntries = List.allDistinctBy(x -> x, value)", lines),
                new OwnCheck("data Tree = List<Tree>\ndata V = List<Tree>",
                        "distinctTrees = List.allDistinctBy(x -> x, value)", List.of(List.of(), List.of())),
                new OwnCheck("data Line = { product: String, qty: Int }\ndata V = List<Line>",
                        "uniqueProducts = List.allDistinctBy(.product, value)",
                        List.of(Map.of("product", "a", "qty", 1L), Map.of("product", "a", "qty", 2L))),
                new OwnCheck("data V = String", "digitsOnly = List.all(c -> c <= 57, String.codePoints(value))", "1a2"));
        for (OwnCheck row : rows) {
            Issue issue = soleIssue(row.declarations() + "\n    invariant " + row.clause() + "\n", row.input());
            assertEquals("invariant_violation", issue.code(), row.clause());
            assertEquals("V", issue.meta().get("type"), row.clause());
            assertEquals(row.clause().substring(0, row.clause().indexOf(' ')), issue.meta().get("clause"));
            assertFalse(issue.customMessage(), "an invariant's text must stay replaceable");
        }
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
        assertNull(issue.meta().get("clause"), "a clause declared without a name has none to report");
        // the same replaceability the mapped constraints have: refine's message overload would mint a
        // custom-message issue that a resolver refuses to touch, so the failure is built by hand
        assertFalse(issue.customMessage(), "an invariant's text must stay replaceable");
        assertEquals("resolved", issue.resolve((code, meta) -> "resolved").message());
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
    void aPatternIsBuiltOncePerDecoderNotPerDecode() {
        // The constraint chain is rebuilt on every decode call, so a machine built there would be
        // built again per value; it is a dynamic constant of the decoder, which the JVM resolves
        // once and answers from its pool after that.
        Map<String, ClassFileImage> classes = Compiler.compile("""
                module demo

                data V = String
                    invariant String.matches("[0-9]{3}", value)
                """);
        ClassModel dec = ClassFile.of().parse(
                classes.get(Emitted.decoder("demo", "V", DecoderKind.VALUE)).bytes());
        int patterns = 0;
        for (PoolEntry entry : dec.constantPool()) {
            if (entry instanceof ConstantDynamicEntry constant
                    && constant.bootstrap().bootstrapMethod().reference().owner().asSymbol()
                            .equals(ClassDesc.of("souther.runtime.Patterns"))) {
                patterns++;
            }
        }
        assertEquals(1, patterns, "the invariant's pattern is one dynamic constant of the decoder");
    }

    /** Two patterns are two constants, whatever their texts: `Aa` and `BB` hash alike, and so would
     *  any text written from them the same way. */
    @Test
    void twoPatternsAreKeptApartThoughTheirTextsHashAlike() throws Exception {
        Issue issue = soleIssue("""
                data V = String
                    invariant first = String.matches(".*Aa.*", value)
                    invariant second = String.matches(".*BB.*", value)
                """, "Aa");
        assertEquals("invalid_format", issue.code());
        assertEquals(".*BB.*", issue.meta().get("pattern"),
                "the second pattern, held apart from the first");
    }

    /** Every constraint of a list is one a decoder can be asked for after a uniqueness. A constraint
     * added to {@code OfList} has no clause here until one is written for it, so one that would
     * need the decoder the uniqueness no longer answers is found by loading it, not by a user. */
    @Test
    void everyListConstraintLoadsAfterAUniqueness() throws Exception {
        Map<Class<?>, String> clauses = Map.of(
                BoundaryConstraint.NonEmpty.class, "List.length(value) >= 1",
                BoundaryConstraint.MinSize.class, "List.length(value) >= 2",
                BoundaryConstraint.MaxSize.class, "List.length(value) <= 2",
                BoundaryConstraint.FixedSize.class, "List.length(value) == 2");
        List<Class<?>> others = new ArrayList<>(
                List.of(BoundaryConstraint.OfList.class.getPermittedSubclasses()));
        others.remove(BoundaryConstraint.Unique.class);
        assertEquals(new HashSet<>(others), clauses.keySet(),
                "a list constraint with no clause written to follow a uniqueness");
        for (String clause : clauses.values()) {
            Result<?> r = decoded("""
                    data V = List<Int>
                        invariant List.allDistinctBy(x -> x, value)
                        invariant %s
                    """.formatted(clause), List.of(1L, 2L));
            assertTrue(r instanceof Ok, clause);
        }
    }

    private static List<List<Integer>> orders(int n) {
        List<List<Integer>> out = new ArrayList<>();
        extend(new ArrayList<>(), n, out);
        return out;
    }

    private static void extend(List<Integer> prefix, int n, List<List<Integer>> out) {
        if (prefix.size() == n) {
            out.add(List.copyOf(prefix));
            return;
        }
        for (int i = 0; i < n; i++) {
            if (!prefix.contains(i)) {
                prefix.add(i);
                extend(prefix, n, out);
                prefix.removeLast();
            }
        }
    }

    private static String declared(String head, List<String> clauses, List<Integer> order) {
        StringBuilder data = new StringBuilder(head);
        for (int i : order) {
            data.append("    invariant ").append(clauses.get(i)).append('\n');
        }
        return data.toString();
    }

    /**
     * The failure reported is the first clause, in the order the clauses are declared, that the value
     * breaks, and it is the issue that clause gives on its own — whether the clause is stated as a
     * Raoh constraint or is checked as itself, and whichever side of the other it is declared.
     * {@code __construct} decides in the same order, so the boundary and an attempted construction
     * name the same clause for the same value. Every order of the clauses is tried.
     */
    private static void theFirstClauseThatFailsInDeclarationOrderIsReported(
            String head, List<String> clauses, List<Object> inputs) throws Exception {
        List<Decoder<Object, ?>> alone = new ArrayList<>();
        for (int i = 0; i < clauses.size(); i++) {
            alone.add(decoderOf(declared(head, clauses, List.of(i))));
        }
        for (List<Integer> order : orders(clauses.size())) {
            Decoder<Object, ?> together = decoderOf(declared(head, clauses, order));
            for (Object input : inputs) {
                Optional<Issue> expected = Optional.empty();
                for (int i : order) {
                    expected = issueOf(alone.get(i), input);
                    if (expected.isPresent()) {
                        break;
                    }
                }
                assertEquals(expected, issueOf(together, input), order + " on " + input);
            }
        }
    }

    @Test
    void theFirstStringClauseToFailIsTheOneReported() throws Exception {
        theFirstClauseThatFailsInDeclarationOrderIsReported("data V = String\n",
                List.of("digitsOnly = List.all(c -> c <= 57, String.codePoints(value))",
                        "String.length(value) >= 5",
                        "String.length(value) <= 6",
                        "String.matches(\"[0-9]+\", value)"),
                List.of("", "1a2", "123", "123456", "1234567", "abcdefg", "12345"));
    }

    @Test
    void theFirstListClauseToFailIsTheOneReported() throws Exception {
        theFirstClauseThatFailsInDeclarationOrderIsReported("data V = List<Int>\n",
                List.of("List.allDistinctBy(x -> x, value)",
                        "List.length(value) <= 2",
                        "List.length(value) >= 2",
                        "positive = List.all(n -> n > 0, value)"),
                List.of(List.of(), List.of(1L), List.of(1L, 2L), List.of(1L, 1L), List.of(1L, 1L, 1L),
                        List.of(1L, 2L, 3L), List.of(0L, 1L), List.of(0L, 0L, 1L)));
    }

    @Test
    void theFirstMapClauseToFailIsTheOneReported() throws Exception {
        theFirstClauseThatFailsInDeclarationOrderIsReported("data V = Map<String, Int>\n",
                List.of("notThree = Bool.not(Map.size(value) == 3)",
                        "Map.size(value) <= 2",
                        "Map.size(value) >= 1"),
                List.of(Map.of(), Map.of("a", 1L), Map.of("a", 1L, "b", 2L),
                        Map.of("a", 1L, "b", 2L, "c", 3L), Map.of("a", 1L, "b", 2L, "c", 3L, "d", 4L)));
    }

    /** The rules written as one clause are the same chain as the same rules written as clauses. */
    @Test
    void clausesWrittenAsOneAreChainedLikeClausesDeclaredSeparately() throws Exception {
        List<String> clauses = List.of("List.allDistinctBy(x -> x, value)", "List.length(value) <= 2",
                "List.length(value) >= 2");
        List<Object> inputs = List.of(List.of(), List.of(1L), List.of(1L, 2L), List.of(1L, 1L),
                List.of(1L, 1L, 1L), List.of(1L, 2L, 3L));
        for (List<Integer> order : orders(clauses.size())) {
            Decoder<Object, ?> separately = decoderOf(declared("data V = List<Int>\n", clauses, order));
            StringBuilder one = new StringBuilder("data V = List<Int>\n    invariant ");
            for (int i = 0; i < order.size(); i++) {
                one.append(i == 0 ? "" : " && ").append(clauses.get(order.get(i)));
            }
            Decoder<Object, ?> joined = decoderOf(one.append('\n').toString());
            for (Object input : inputs) {
                assertEquals(issueOf(separately, input), issueOf(joined, input), order + " on " + input);
            }
        }
    }

    /** An emptiness check denied, and a size held unequal to nought, are the non-emptiness a size
     *  of at least one is: the same constraint, reported the same way. */
    @Test
    void aDeniedEmptinessCheckIsANonEmptiness() throws Exception {
        String least = """
                data V = List<Int>
                    invariant List.length(value) >= 1
                """;
        for (String rule : List.of("Bool.not(List.isEmpty(value))", "List.isEmpty(value) == false",
                "List.length(value) /= 0")) {
            String denied = least.replace("List.length(value) >= 1", rule);
            assertEquals(soleIssue(least, List.of()), soleIssue(denied, List.of()), rule);
            assertTrue(decoded(denied, List.of(1L)) instanceof Ok, rule);
        }
    }

    /** The same rule written as the law the call comes to — as many different elements as
     *  elements — and shown to answer for every list, is the same constraint, reported the same
     *  way. */
    @Test
    void aRepeatedElementOfARuleWrittenByCountIsADuplicate() throws Exception {
        String call = """
                data V = List<Int>
                    invariant List.allDistinctBy(x -> x, value)
                """;
        for (String rule : List.of("Set.size(Set.fromList(value)) == List.length(value)",
                "List.length(value) == Set.size(Set.fromList(value))",
                "2 * Set.size(Set.fromList(value)) == 2 * List.length(value)")) {
            String counted = call.replace("List.allDistinctBy(x -> x, value)", rule);
            assertEquals(soleIssue(call, List.of(1L, 2L, 1L)),
                    soleIssue(counted, List.of(1L, 2L, 1L)), rule);
            assertTrue(decoded(counted, List.of(1L, 2L)) instanceof Ok, rule);
        }
    }

    /**
     * A rule that keeps the elements apart where it answers and is not shown to answer for every
     * list is no constraint: the decoder works the clause out, and a list it stops on stops there
     * as it would without the reading — a repeat included, which the constraint would have
     * reported as a repeat instead. A count multiplied past what an {@code Int} holds, and a key
     * filed beside a number added past it, are two such rules. A count through
     * {@code List.distinct} is not: the library shows the walk keeping the first of each answers
     * for every list, so a repeat is reported as one.
     */
    @Test
    void aRuleNotShownToAnswerForEveryListIsWorkedOutAsItIs() throws Exception {
        for (String rule : List.of(
                "9223372036854775807 * Set.size(Set.fromList(value))"
                        + " == 9223372036854775807 * List.length(value)",
                "Map.size(Map.fromList(List.map(x -> (x, 9223372036854775807 + x), value)))"
                        + " == List.length(value)")) {
            String data = "data V = List<Int>\n    invariant " + rule + "\n";
            for (List<Long> stops : List.of(List.of(0L, 1L), List.of(1L, 1L))) {
                ConstraintViolation thrown = assertThrows(ConstraintViolation.class,
                        () -> decoded(data, stops), rule + " " + stops);
                assertTrue(thrown.getMessage().startsWith("Int overflow"),
                        () -> rule + " " + stops + ": " + thrown);
            }
        }
        String distinct = """
                data V = List<Int>
                    invariant List.length(List.distinct(value)) == List.length(value)
                """;
        assertTrue(decoded(distinct, List.of(1L, 2L)) instanceof Ok);
        assertEquals("duplicate_element", firstIssue(decoded(distinct, List.of(1L, 2L, 1L))).code(),
                "read as the constraint, which says which element repeats");
    }

    /** A key that does not decode leaves no map of the model's for a clause to be about, so it is
     *  what is reported, and the size of the object it came in is not asked. */
    @Test
    void aKeyThatDoesNotDecodeIsReportedBeforeTheMapsSize() throws Exception {
        Issue issue = soleIssue("""
                data K = String
                    invariant String.length(value) >= 2
                data V = Map<K, Int>
                    invariant Map.size(value) >= 2
                """, Map.of("a", 1L));
        assertEquals("too_short", issue.code(), "the key's own rule, not the map's size");
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
        Decoder<Object, ?> dec = decoderOf(data);

        // 𠮷田: two characters, four UTF-16 units. The model admits it, so the decoder must too.
        assertTrue(dec.decode("𠮷田", Path.ROOT) instanceof Ok,
                "a two-code-point value inside a bound of 2 must decode");

        Issue issue = soleIssue(data, "𠮷田山");   // 𠮷田山: three characters
        assertEquals("too_long", issue.code());
        assertEquals(3, issue.meta().get("actual"), "the reported length is in code points");
    }
}
