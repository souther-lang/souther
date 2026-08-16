package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.WrittenAt;
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
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every word the shipped schema allows is one somebody accounted for.
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
 *
 * <p>Which is why a word may outlive the constant it spelled. A version says what its documents may
 * carry, and a report written before a rename carries the old word for as long as anyone keeps it. So
 * the schema is what the compiler writes now together with what it wrote then, and the second half is
 * named here — a word that quietly stopped being emitted still fails, and one kept on purpose is one
 * somebody wrote down.
 *
 * <p>The correspondence was an equality until a code was renamed after the field it sits in had
 * reached a published report. Before that every word taken out had never been emitted, so there was
 * nothing for a document to be holding, and the schema was corrected rather than versioned.
 */
class EverySchemaWordIsAccountedForTest {

    private static final String SCHEMA = "/souther/adequacy-schema-1.json";
    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One enumerated field, and the enum whose constants it spells.
     *
     * @param at the field, as the keys leading to it from the root of the schema
     */
    private record Vocabulary(String label, List<String> at, Class<?> source,
                              Set<String> written, Set<String> retired) {

        Vocabulary(String label, List<String> at, Class<?> source) {
            this(label, at, source, null, Set.of());
        }

        Vocabulary(String label, List<String> at, Class<?> source,
                   Set<String> retired) {
            this(label, at, source, null, retired);
        }

        /** A field whose words are not an enum's own names. {@link #source} is what they are
         * projected from, named so a reader knows where to look, and not what they are spelled by. */
        Vocabulary(String label, List<String> at, Set<String> written) {
            this(label, at, MeasurementStatus.class, written, Set.of());
        }

        /** Every word a document of this version may carry: what is written now, and what was. */
        Set<String> allowed() {
            Set<String> out = new LinkedHashSet<>(written == null ? wordsOf(source) : written);
            out.addAll(retired);
            return out;
        }
    }

    /** The kinds of site a branch measure counts, spelled by the writer's own encoder. */
    private static Set<String> armWords() {
        return Arrays.stream(CoverageSites.Site.Kind.values())
                .filter(CoverageSites.Site.Kind::isArm)
                .map(AdequacyReport::word)
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * What a citation can say about a place, spelled by the one writer of the field.
     *
     * <p>Both arms built rather than listed. These words are not an enum's — they are what the
     * citation writes — so a list here would be a second copy of them, and the schema would go on
     * agreeing with the copy after the writer had stopped saying it.
     */
    private static Set<String> writtenAtWords() {
        SourcePos here = new SourcePos(1, 1, "s");
        return java.util.stream.Stream
                .of(here, here.standingInFor(WrittenAt.outOfSight(new SourceProvenance.TheStandardLibrary("List.filter"))))
                .map(pos -> Citation.of(pos).writtenAtFields().get("kind"))
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    /** What a document may say a status is. Two of the compiler's four states share one of them. */
    private static final Set<String> STATUS_WORDS =
            new LinkedHashSet<>(List.of("complete", "partial", "unavailable"));

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
            // `status` is the one enumerated field written through a projection rather than off an
            // enum's own names. The compiler tells a measure with nothing to be about from one nobody
            // made; a document says `unavailable` for both and leaves which to the `reason` beside it.
            // So the words here are the projection's image, which
            // `theStatusWordsAreWhatTheWriterCanWrite` holds against the writer — naming a state
            // inside the compiler is not a change to the contract, and would be one if this read
            // the constants.
            new Vocabulary("status", List.of("$defs", "status"), STATUS_WORDS),
            new Vocabulary("branch.reason", List.of("$defs", "branch", "properties", "reason"),
                    Adequacy.BranchEvidence.Reason.class),
            // The arms, which is fewer than the kinds a site has. A comparison of a guard's condition
            // is a site and not a fork a row is in or out of, so it never reaches this field —
            // projected off the same predicate the measure uses rather than listed here, so that an
            // arm kind added later still has to teach the schema its word.
            new Vocabulary("branch.unreached[].kind",
                    List.of("$defs", "branch", "properties", "unreached", "items", "properties",
                            "kind"),
                    CoverageSites.Site.Kind.class, armWords(), Set.of()),
            new Vocabulary("partition.axesMeasure.reason",
                    List.of("$defs", "partition", "properties", "axesMeasure", "properties",
                            "reason"),
                    PartitionEvidence.Partitioned.Reason.class),
            new Vocabulary("partition.notRead[].reason",
                    List.of("$defs", "partition", "properties", "notRead", "items", "properties",
                            "reason"),
                    souther.compiler.partition.UndividedPosition.Reason.class),
            new Vocabulary("partition.boundariesMeasure.reason",
                    List.of("$defs", "partition", "properties", "boundariesMeasure", "properties",
                            "reason"),
                    PartitionEvidence.Bounded.Reason.class),
            new Vocabulary("partition.axes[].reason",
                    List.of("$defs", "partition", "properties", "axes", "items", "properties",
                            "reason"),
                    PartitionEvidence.AxisCoverage.Reason.class),
            new Vocabulary("partition.boundaries[].side",
                    List.of("$defs", "partition", "properties", "boundaries", "items", "properties",
                            "side"),
                    BoundaryObligation.BoundarySide.class),
            new Vocabulary("partition.boundaries[].kind",
                    List.of("$defs", "partition", "properties", "boundaries", "items", "properties",
                            "kind"),
                    souther.compiler.partition.BoundaryTarget.Shape.class),
            // `no_arm_witnesses_it` was what a guard's line came back as where the arms could not
            // separate the rows that reached its comparison from the rows that did not. The
            // comparison is observed where it runs now, so nothing produces the word — and reports of
            // this version were written carrying it, and a version says what its documents may carry.
            new Vocabulary("partition.boundaries[].reason",
                    List.of("$defs", "partition", "properties", "boundaries", "items", "properties",
                            "reason"),
                    BoundaryAssessment.Coverage.Reason.class, Set.of("no_arm_witnesses_it")),
            new Vocabulary("partition.pairs.reason",
                    List.of("$defs", "partition", "properties", "pairs", "properties", "reason"),
                    PartitionEvidence.PairSpace.Reason.class),
            new Vocabulary("signature.reason", List.of("$defs", "signature", "properties", "reason"),
                    Adequacy.SignatureEvidence.Reason.class),
            new Vocabulary("incompleteness.scope",
                    List.of("$defs", "incompleteness", "properties", "scope"),
                    Incompleteness.Scope.class),
            // `probe_mapping_lost` is what `instrumentation_absent` was called. It is retired
            // rather than gone: reports of this version were written carrying it, and a version
            // says what its documents may carry. Naming it here is what keeps that a decision about
            // the contract — a word that stops being emitted and is not written down still fails.
            new Vocabulary("incompleteness.code",
                    List.of("$defs", "incompleteness", "properties", "code"),
                    Incompleteness.Code.class, Set.of("probe_mapping_lost")),
            // Whether a place is where the code it names is written. Not an enum: the two words
            // are the citation's own, and are read off it rather than listed here.
            new Vocabulary("at.writtenAt.kind",
                    List.of("$defs", "writtenAt", "properties", "kind"),
                    Citation.class, writtenAtWords(), Set.of()));

    /**
     * The status words the schema allows are the ones the writer can write.
     *
     * <p>Held against the writer because that is what a document carries. The list above is what a
     * consumer must handle, and a projection that started answering a fourth word would leave that
     * list true of nothing — the schema and the enum would still agree, and the documents would
     * agree with neither.
     */
    @Test
    void theStatusWordsAreWhatTheWriterCanWrite() {
        Set<String> written = new LinkedHashSet<>();
        for (MeasurementStatus status : MeasurementStatus.values()) {
            written.add(AdequacyReport.wire(status));
        }
        assertEquals(STATUS_WORDS, written);
    }

    @Test
    void everyEnumeratedFieldNamesCurrentOrRetiredWords() {
        JsonNode schema = schema();
        for (Vocabulary each : VOCABULARIES) {
            assertEquals(each.allowed(), allowedAt(schema, each.at()),
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
     * A key added since is optional, which is what keeps an older document a document of this version.
     *
     * <p>The schema says so in its own description: a change that removes or renames anything raises
     * the number, and something added does not, so a report written before a key existed is still one
     * of this version. Requiring an added key breaks that in the file that states it — every earlier
     * document is refused by the schema it was written against.
     *
     * <p>Held as the keys a boundary written before {@code kind} carried, which is the shape the
     * defect took. A key added later and required would fail here rather than on somebody's stored
     * report, and the word test beside this one cannot see it: the words were right, and the document
     * carrying none of them was the one refused.
     */
    @Test
    void aBoundaryWrittenBeforeAKeyExistedIsStillOfThisVersion() {
        Set<String> required = new LinkedHashSet<>();
        for (JsonNode each : nodeAt(schema(),
                List.of("$defs", "partition", "properties", "boundaries", "items", "required"))) {
            required.add(each.asString());
        }

        assertEquals(Set.of("axis", "origin", "side", "value", "hit", "knownWritable", "status"),
                required, "a boundary object written before `kind` existed carries these and no more");
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

        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(souther.compiler.diag.SourceNameResolver.identity()));
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
    private static Set<String> wordsOf(Class<?> source) {
        Object[] constants = source.getEnumConstants();
        if (constants == null) {
            // The type stopped saying this when a field turned up whose words are a writer's and
            // not an enum's. Said here instead, because the alternative was a vocabulary with
            // neither an enum nor a written set failing as a null somewhere inside a stream.
            throw new IllegalArgumentException(source.getSimpleName()
                    + " is not an enum, so a vocabulary over it has to write its words out");
        }
        return Arrays.stream(constants)
                .map(constant -> AdequacyReport.word((Enum<?>) constant))
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    private static Set<String> allowedAt(JsonNode schema, List<String> at) {
        Set<String> out = new LinkedHashSet<>();
        for (JsonNode each : nodeAt(schema, at).get("enum")) {
            out.add(each.asString());
        }
        return out;
    }

    /** The node the keys lead to, which the schema is asserted to have. */
    private static JsonNode nodeAt(JsonNode schema, List<String> at) {
        JsonNode node = schema;
        for (String key : at) {
            node = node.get(key);
            assertNotNull(node, "the schema has no " + String.join("/", at));
        }
        return node;
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
        try (InputStream in = AdequacyReport.class.getResourceAsStream(SCHEMA)) {
            assertNotNull(in, "adequacy-schema-1.json ships beside the compiler");
            return JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (java.io.IOException e) {
            throw new AssertionError(e);
        }
    }
}
