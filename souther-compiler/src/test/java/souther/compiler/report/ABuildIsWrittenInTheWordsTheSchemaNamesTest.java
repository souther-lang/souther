package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.DocumentShape;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.RegionSlot;
import souther.compiler.types.RuleOrigin;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.SourceReferenceOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.JsonNodeFactory;
import tools.jackson.databind.node.ObjectNode;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A construct inside a build of a value is written with the steps it was copied by, and each step
 * carries what tells one region from every other.
 *
 * <p>What the keys are is written here rather than read out of the schema. Asked of the schema, the
 * question would be whether the writer agrees with it, and a schema that demanded nothing would be
 * agreed with by a writer that said nothing — which is the state this is here to refuse. So the
 * keys are stated, the writer is held to them, and the schema is held to them beside it.
 *
 * <p>The conformance corpus holds no decision inside a built value, so nothing else writes one out
 * — the checks that a document naming a region wrongly is refused splice one into a document the
 * corpus does check in, rather than compiling a program that reaches the shape.
 */
class ABuildIsWrittenInTheWordsTheSchemaNamesTest {

    private static final WrittenOwner.Body OWNER = new WrittenOwner.Body("m", "f");

    private static final ValueName VALUE = new ValueName.Helper("m", "inner");

    private static final SourceConstructOrigin FORK =
            SourceConstructOrigin.written(OWNER, 3, SourceConstruct.IF);

    private static final SourceConstructOrigin CALL =
            SourceConstructOrigin.written(OWNER, 5, SourceConstruct.CALL);

    /** Each region a build can be made for, and what a document has to say to name it. */
    private static final Map<MaterialisationSite, Set<String>> NAMED_BY = namedBy();

    private static Map<MaterialisationSite, Set<String>> namedBy() {
        Map<MaterialisationSite, Set<String>> out = new LinkedHashMap<>();
        // A definition's body is named by the definition, module and all: two definitions' bodies
        // are two regions.
        out.put(new MaterialisationSite.Body(OWNER), Set.of("kind", "module", "definition"));
        // A region a construct opens is named by the construct and which of its regions this is.
        // The construct takes its lowered number with it, a lowering making several forks of one.
        Set<String> slot = Set.of("kind", "module", "definition", "construct", "lowered", "slot");
        for (RegionSlot each : List.of(new RegionSlot.IfThen(), new RegionSlot.IfElse(),
                new RegionSlot.ConstructedThen(), new RegionSlot.ConstructedElse(Optional.empty()),
                new RegionSlot.ShortCircuitRight(), new RegionSlot.ComprehensionElement())) {
            out.put(new MaterialisationSite.Slot(FORK, each), slot);
        }
        // And two of them say more, because the slot alone does not tell their regions apart.
        out.put(new MaterialisationSite.Slot(FORK, new RegionSlot.MatchCase(List.of("Yes", "No"))),
                with(slot, "cases"));
        out.put(new MaterialisationSite.Slot(FORK, new RegionSlot.ComprehensionGuard(1)),
                with(slot, "index"));
        // The clause a refused arm answers for, where it answers for one rather than for any.
        out.put(new MaterialisationSite.Slot(FORK,
                new RegionSlot.ConstructedElse(Optional.of("positive"))), with(slot, "clause"));
        // A block the author wrote is named by its rule, and one written out of a name by which
        // reference of that definition the name is.
        out.put(new MaterialisationSite.WrittenBlock(RuleOrigin.written(OWNER, 2)),
                Set.of("kind", "module", "definition", "rule"));
        out.put(new MaterialisationSite.GeneratedBlock(new SourceReferenceOrigin(OWNER, 4)),
                Set.of("kind", "module", "definition", "reference"));
        return out;
    }

    private static Set<String> with(Set<String> keys, String more) {
        Set<String> out = new TreeSet<>(keys);
        out.add(more);
        return out;
    }

    private static JsonNode written(MaterialisationSite site) {
        OccurrenceLineage lineage = OccurrenceLineage.ORIGINAL
                .builtFor(VALUE, site)
                .copiedInto(new ValueName.Helper("m", "same"), new ExpansionSite.Written(CALL));
        ObjectNode into = JsonNodeFactory.instance.objectNode();
        AdequacyReport.constructId(into, new ConstructOccurrence(
                SourceConstructOrigin.written(new WrittenOwner.Body("m", "inner"), 0,
                        SourceConstruct.BINARY),
                lineage));
        return into;
    }

    private static Set<String> names(JsonNode object) {
        Set<String> out = new TreeSet<>();
        object.propertyNames().forEach(out::add);
        return out;
    }

    @Test
    void everyRegionIsWrittenWithWhatNamesIt() {
        List<String> wrong = new ArrayList<>();
        NAMED_BY.forEach((site, keys) -> {
            JsonNode step = written(site).get("through").get(0);
            if (!"materialisation".equals(step.get("kind").asString())) {
                wrong.add(site + " is not written as a build");
                return;
            }
            if (!names(step.get("at")).equals(new TreeSet<>(keys))) {
                wrong.add(site + " is written with " + names(step.get("at")) + ", not " + keys);
            }
        });

        assertEquals(List.of(), wrong);
    }

    /**
     * And the schema demands each of them, so a document naming a region by less is refused rather
     * than read as one more region nobody can tell from another.
     *
     * <p>Except the clause a refused arm answers for. One arm of an attempted construction answers
     * for any failure and names no clause, so its absence is what says which arm that is — demanded,
     * it would refuse the arm the key exists to tell from the others.
     */
    @Test
    void theSchemaDemandsWhatNamesEachRegion() {
        JsonNode region = DocumentShape.schema().get("$defs").get("materialisationRegion");
        List<String> wrong = new ArrayList<>();
        NAMED_BY.forEach((site, keys) -> {
            JsonNode at = written(site).get("through").get(0).get("at");
            Set<String> demanded = with(demandedFor(region, at), "clause");
            if (!demanded.containsAll(keys)) {
                wrong.add(site + " is named by " + keys + " and the schema demands " + demanded);
            }
        });

        assertEquals(List.of(), wrong);
    }

    /** What the schema requires of an object shaped like {@code of}: its own list, and each one a
     *  branch whose condition {@code of} meets adds. */
    private static Set<String> demandedFor(JsonNode schema, JsonNode of) {
        Set<String> out = new TreeSet<>();
        schema.optional("required").ifPresent(
                required -> required.forEach(key -> out.add(key.asString())));
        schema.optional("allOf").ifPresent(branches -> branches.forEach(branch -> {
            if (meets(branch.get("if"), of)) {
                out.addAll(demandedFor(branch.get("then"), of));
            }
        }));
        return out;
    }

    /** Whether {@code of} takes the branch {@code condition} selects, which here is one or more
     *  keys each holding a word from a {@code const} or an {@code enum}. */
    private static boolean meets(JsonNode condition, JsonNode of) {
        JsonNode properties = condition.get("properties");
        for (String key : names(properties)) {
            if (!of.has(key)) {
                return false;
            }
            JsonNode said = properties.get(key);
            String held = of.get(key).asString();
            boolean matches = said.has("const") ? said.get("const").asString().equals(held)
                    : anyIs(said.get("enum"), held);
            if (!matches) {
                return false;
            }
        }
        return true;
    }

    private static boolean anyIs(JsonNode words, String word) {
        for (JsonNode each : words) {
            if (word.equals(each.asString())) {
                return true;
            }
        }
        return false;
    }

    @Test
    void theStepsAreWrittenInTheOrderTheCopyWasMade() {
        JsonNode through = written(new MaterialisationSite.Body(OWNER)).get("through");

        assertEquals(2, through.size());
        assertEquals("materialisation", through.get(0).get("kind").asString());
        assertEquals("expansion", through.get(1).get("kind").asString());
    }

    @Test
    void anExpansionStepKeepsTheKeysItAlwaysHad() {
        JsonNode step = written(new MaterialisationSite.Body(OWNER)).get("through").get(1);

        assertEquals(Set.of("kind", "expanded", "module", "definition", "call", "lowered"),
                names(step));
    }

    /** A build says nothing a call says: the two are told apart by the kind and never by what
     *  happens to be beside it. */
    @Test
    void aBuildCarriesNoneOfACallsKeys() {
        JsonNode build = written(new MaterialisationSite.Body(OWNER)).get("through").get(0);

        assertEquals(Set.of("kind", "materialised", "at"), names(build));
    }

    /** Every key any region is named by, across every arm. */
    private static final Set<String> EVERY_REGION_KEY = NAMED_BY.values().stream()
            .flatMap(Set::stream).collect(Collectors.toCollection(TreeSet::new));

    /**
     * A region named with a key another arm uses, and this one does not, is refused.
     *
     * <p>{@code containsAll} is not enough to guard this: it is met by a schema that demands the
     * region's own keys and allows every arm's keys besides, which is a schema two of these could
     * still be written under. What is checked here is the other half — that a document adding one
     * such key is one the schema no longer takes.
     *
     * <p>Except {@code clause} on a {@code constructed_else} region, which is not another arm's key
     * leaking in: it is this arm's own, present on the one this map named by it and absent on the
     * one named without it, and that absence is what tells the two apart.
     */
    @Test
    void theSchemaRefusesARegionNamedWithAnotherArmsKey() {
        List<String> wrong = new ArrayList<>();
        NAMED_BY.forEach((site, keys) -> {
            for (String stray : EVERY_REGION_KEY) {
                if (keys.contains(stray) || isTheOptionalClauseOfItsOwnArm(site, stray)) {
                    continue;
                }
                ObjectNode at = (ObjectNode) written(site).get("through").get(0).get("at");
                withStray(at, stray);
                if (DocumentShape.of(spliced(at)).wrong().isEmpty()) {
                    wrong.add(site + " is still accepted with a stray `" + stray + "`");
                }
            }
        });

        assertEquals(List.of(), wrong);
    }

    private static boolean isTheOptionalClauseOfItsOwnArm(MaterialisationSite site, String key) {
        return "clause".equals(key) && site instanceof MaterialisationSite.Slot slot
                && slot.slot() instanceof RegionSlot.ConstructedElse;
    }

    /** {@code at}, with {@code key} added at a value of the shape its own schema entry asks for —
     *  so a document is wrong only for carrying the key at all and not for the shape under it. */
    private static void withStray(ObjectNode at, String key) {
        switch (key) {
            case "construct", "lowered", "index", "rule", "reference" -> at.put(key, 0);
            case "cases" -> at.putArray(key).add("Yes");
            default -> at.put(key, "x");
        }
    }

    /**
     * A real, checked-in, schema-shaped document with its one {@code through} array replaced by a
     * build naming {@code at}.
     *
     * <p>A document built by hand for this alone would have to restate every key a document is
     * asked for around a decision — the module's own status, its declarations, a behavior's
     * partition, everything the schema demands elsewhere — and would be answering none of what this
     * test is about. So this takes a document {@code soIsEveryAnswerCheckedIn} already holds to the
     * schema, and touches only the one array whose shape is in question.
     */
    private static JsonNode spliced(JsonNode at) {
        ObjectNode document = (ObjectNode) checkedInDocument().deepCopy();
        ObjectNode step = JsonNodeFactory.instance.objectNode();
        step.put("kind", "materialisation");
        step.put("materialised", "m.v");
        step.set("at", at);
        ArrayNode through = (ArrayNode) throughArrayOf(document);
        through.removeAll();
        through.add(step);
        return document;
    }

    /** The first {@code through} array {@code node} holds, at any depth. */
    private static JsonNode throughArrayOf(JsonNode node) {
        if (node.isObject() && node.has("through") && node.get("through").isArray()) {
            return node.get("through");
        }
        for (JsonNode child : node.isObject() ? node.properties().stream().map(Map.Entry::getValue)
                .toList() : node.isArray() ? toList(node) : List.<JsonNode>of()) {
            JsonNode found = throughArrayOf(child);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    private static List<JsonNode> toList(JsonNode array) {
        List<JsonNode> out = new ArrayList<>();
        array.forEach(out::add);
        return out;
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** A document {@code TheAnswersAboutEachConformanceCorpusAreTheOnesCheckedInTest} already
     *  holds the shipped schema to. Read fresh, since a caller of {@link #spliced} deep-copies it
     *  before mutating anything. */
    private static JsonNode checkedInDocument() {
        try (var in = ABuildIsWrittenInTheWordsTheSchemaNamesTest.class.getResourceAsStream(
                "/souther/compiler/conformance/catalog/expected.report.json")) {
            return JSON.readTree(in.readAllBytes());
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
