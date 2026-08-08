package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The words the shipped schema allows are the words the compiler writes.
 *
 * <p>Every enumerated field of {@code adequacy-schema-1.json} is a second spelling of a Java enum.
 * The two are edited in different files by different hands, and until this test nothing noticed when
 * one moved: `ROW_TIMED_OUT` became `ROW_UNDECIDED` when a row stopped being held to a clock, the
 * rename was right, and the schema went on promising a word that had not been emitted since.
 *
 * <p>Held as a correspondence rather than by generating one side from the other. A published contract
 * generated from an internal enum would change whenever the internal enum did, which is the opposite
 * mistake: renaming a constant is a decision about the compiler, and widening what a consumer must
 * handle is a decision about the contract. This makes the second decision impossible to take by
 * accident, and leaves both deliberate.
 */
class EveryWordTheSchemaAllowsIsOneTheCompilerWritesTest {

    private static final String SCHEMA = "/souther/adequacy-schema-1.json";
    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One enumerated field, and the enum whose constants it spells.
     *
     * @param at the field, as the keys leading to it from the root of the schema
     */
    private record Vocabulary(String label, List<String> at, Class<? extends Enum<?>> source) {}

    /**
     * Every enumerated field the schema has.
     *
     * <p>Written out rather than discovered. A test that walked the schema for `enum` and looked for
     * something to compare each against would pass over a field it could not place, which is the
     * field most worth knowing about — one nobody has said where the words come from.
     */
    private static final List<Vocabulary> VOCABULARIES = List.of(
            new Vocabulary("adequacy", List.of("properties", "adequacy"),
                    AdequacyReport.AdequacyStatus.class),
            new Vocabulary("status", List.of("$defs", "status"),
                    MeasurementStatus.class),
            new Vocabulary("branch.reason", List.of("$defs", "branch", "properties", "reason"),
                    Adequacy.BranchEvidence.Reason.class),
            new Vocabulary("branch.unreached[].kind",
                    List.of("$defs", "branch", "properties", "unreached", "items", "properties",
                            "kind"),
                    CoverageSites.Site.Kind.class),
            new Vocabulary("partition.axes[].reason",
                    List.of("$defs", "partition", "properties", "axes", "items", "properties",
                            "reason"),
                    PartitionEvidence.AxisCoverage.Reason.class),
            new Vocabulary("partition.boundaries[].side",
                    List.of("$defs", "partition", "properties", "boundaries", "items", "properties",
                            "side"),
                    BoundaryObligation.BoundarySide.class),
            new Vocabulary("partition.boundaries[].reason",
                    List.of("$defs", "partition", "properties", "boundaries", "items", "properties",
                            "reason"),
                    BoundaryAssessment.Coverage.Reason.class),
            new Vocabulary("partition.pairs.reason",
                    List.of("$defs", "partition", "properties", "pairs", "properties", "reason"),
                    PartitionEvidence.PairSpace.Reason.class),
            new Vocabulary("signature.reason", List.of("$defs", "signature", "properties", "reason"),
                    Adequacy.SignatureEvidence.Reason.class),
            new Vocabulary("incompleteness.scope",
                    List.of("$defs", "incompleteness", "properties", "scope"),
                    Incompleteness.Scope.class),
            new Vocabulary("incompleteness.code",
                    List.of("$defs", "incompleteness", "properties", "code"),
                    Incompleteness.Code.class));

    @Test
    void everyEnumeratedFieldSpellsTheEnumItComesFrom() {
        JsonNode schema = schema();
        for (Vocabulary each : VOCABULARIES) {
            assertEquals(wordsOf(each.source()), allowedAt(schema, each.at()),
                    each.label() + ": the schema and " + each.source().getSimpleName()
                            + " name different words");
        }
    }

    /**
     * The one enumerated field with no enum behind it.
     *
     * <p>{@code implementation} is written from a boolean — a behavior has a {@code let} or it does
     * not — so there is nothing to hold it against. Named here rather than left out, because a field
     * absent from the table above and absent from the schema are indistinguishable to a reader, and
     * only one of them is deliberate.
     */
    @Test
    void theFieldWithNoEnumBehindItIsTheOneThatIsWrittenFromABoolean() {
        assertEquals(Set.of(AdequacyReport.implementationWord(false),
                        AdequacyReport.implementationWord(true)),
                allowedAt(schema(), List.of("$defs", "behavior", "properties", "implementation")));
    }

    /** Every enumerated field of the schema is either held above or named as the exception. */
    @Test
    void noEnumeratedFieldIsUnaccountedFor() {
        List<String> paths = new ArrayList<>();
        collectEnums(schema(), "", paths);
        Set<String> held = new LinkedHashSet<>();
        for (Vocabulary each : VOCABULARIES) {
            held.add("/" + String.join("/", each.at()));
        }
        held.add("/$defs/behavior/properties/implementation");

        List<String> unaccounted = paths.stream().filter(p -> !held.contains(p)).toList();
        assertEquals(List.of(), unaccounted,
                "an enumerated field nothing says where the words come from");
    }

    /**
     * A report that carries an incompleteness says it in a word the schema allows.
     *
     * <p>The end of the same defect, from the other side. What the schema promised and what the
     * compiler wrote could disagree for as long as they did partly because the report the schema is
     * checked against is a clean compile: `incompleteness` is an empty array in it, so the field
     * where the two had come apart was never written at all.
     */
    @Test
    void anUndecidedRowIsReportedInAWordTheSchemaAllows() {
        Compilation compilation = Compilation.ofSource("""
                module example.loop

                data N = Int
                    invariant value >= 0

                data Ok = { n: Int }

                behavior go : (n: N) -> Ok
                    constructs Ok

                let go (n) = Ok { n = n.value }

                example go
                    | "one" : (N(1)) -> Ok { n = 1 }
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.withDeadline(
                DoesNotComeBack.overrunningOn(DoesNotComeBack.everythingAboutRowsOf("go")));
        compilation.answerEverything();

        JsonNode report = JSON.readTree(AdequacyReport.of(compilation).json());
        Set<String> allowed =
                allowedAt(schema(), List.of("$defs", "incompleteness", "properties", "code"));

        List<String> written = new ArrayList<>();
        for (JsonNode module : report.get("modules")) {
            for (JsonNode gap : module.get("incompleteness")) {
                written.add(gap.get("code").asString());
            }
        }
        // The word itself, and not merely a word the schema happens to allow. This is here to keep
        // one reproduction alive: a fixture that stopped producing an undecided row and produced
        // some other legitimate gap instead would go on passing while covering nothing.
        assertEquals(List.of("row_undecided"), written,
                "the row did not come back, and this is what the report says about it");
        assertTrue(allowed.containsAll(written),
                "the schema allows " + allowed + " and the report writes " + written);
    }

    /**
     * The words the report writes for one enum, put through the writer's own encoder.
     *
     * <p>{@link AdequacyReport#word} rather than a second spelling rule written here. A rule written
     * here would agree with the schema while the report wrote something else entirely: what a
     * consumer reads is what the encoder produces, so that is the side a contract has to be held
     * against.
     */
    private static Set<String> wordsOf(Class<? extends Enum<?>> source) {
        return Arrays.stream(source.getEnumConstants())
                .map(AdequacyReport::word)
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    private static Set<String> allowedAt(JsonNode schema, List<String> at) {
        JsonNode node = schema;
        for (String key : at) {
            node = node.get(key);
            assertNotNull(node, "the schema has no " + String.join("/", at));
        }
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode each : node.get("enum")) {
            out.add(each.asString());
        }
        return out;
    }

    /** Every path in the schema that constrains a field to a list of words. */
    private static void collectEnums(JsonNode node, String path, List<String> out) {
        if (node.isObject()) {
            if (node.has("enum")) {
                out.add(path);
            }
            for (String name : node.propertyNames()) {
                collectEnums(node.get(name), path + "/" + name, out);
            }
        } else if (node.isArray()) {
            for (int i = 0; i < node.size(); i++) {
                collectEnums(node.get(i), path + "/" + i, out);
            }
        }
    }

    private static JsonNode schema() {
        try (InputStream in = Main.class.getResourceAsStream(SCHEMA)) {
            assertNotNull(in, "adequacy-schema-1.json ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (java.io.IOException e) {
            throw new AssertionError(e);
        }
    }
}
