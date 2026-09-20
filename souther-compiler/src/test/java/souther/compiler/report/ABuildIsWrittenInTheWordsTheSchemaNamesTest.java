package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.DocumentShape;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.EtaOrigin;
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
import tools.jackson.databind.node.JsonNodeFactory;
import tools.jackson.databind.node.ObjectNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construct inside a build of a value is written with the steps it was copied by, and each of them
 * is said in the words the shipped schema names for it.
 *
 * <p>The conformance corpus holds no decision inside a built value, so nothing else writes one out.
 * What is checked is the object a step becomes against the definitions the schema gives it: every
 * key it carries is one they list, every key they require is there, and the words are ones they
 * allow.
 */
class ABuildIsWrittenInTheWordsTheSchemaNamesTest {

    private static final WrittenOwner.Body OWNER = new WrittenOwner.Body("m", "f");

    private static final ValueName VALUE = new ValueName.Helper("m", "inner");

    private static final SourceConstructOrigin FORK =
            SourceConstructOrigin.written(OWNER, 3, SourceConstruct.IF);

    private static final SourceConstructOrigin CALL =
            SourceConstructOrigin.written(OWNER, 5, SourceConstruct.CALL);

    private static final List<MaterialisationSite> SITES = List.of(
            new MaterialisationSite.Body(OWNER),
            new MaterialisationSite.Slot(FORK, new RegionSlot.IfThen()),
            new MaterialisationSite.Slot(FORK, new RegionSlot.IfElse()),
            new MaterialisationSite.Slot(FORK, new RegionSlot.ConstructedThen()),
            new MaterialisationSite.Slot(FORK,
                    new RegionSlot.ConstructedElse(Optional.of("positive"))),
            new MaterialisationSite.Slot(FORK, new RegionSlot.ConstructedElse(Optional.empty())),
            new MaterialisationSite.Slot(FORK, new RegionSlot.MatchCase(List.of("Yes", "No"))),
            new MaterialisationSite.Slot(FORK, new RegionSlot.ShortCircuitRight()),
            new MaterialisationSite.Slot(FORK, new RegionSlot.ComprehensionElement()),
            new MaterialisationSite.Slot(FORK, new RegionSlot.ComprehensionGuard(1)),
            new MaterialisationSite.WrittenBlock(RuleOrigin.written(OWNER, 2)),
            new MaterialisationSite.GeneratedBlock(
                    new EtaOrigin.Declaration(new SourceReferenceOrigin(OWNER, 4))));

    private static JsonNode written(MaterialisationSite site) {
        OccurrenceLineage lineage = OccurrenceLineage.ORIGINAL
                .builtFor(VALUE, site)
                .copiedInto(new ValueName.Helper("m", "same"),
                        new ExpansionSite.Written(CALL));
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

    private static List<String> words(JsonNode enumeration) {
        List<String> out = new ArrayList<>();
        enumeration.get("enum").forEach(word -> out.add(word.asString()));
        return out;
    }

    @Test
    void everyKindOfRegionIsWrittenAsTheSchemaDefinesIt() {
        JsonNode region = DocumentShape.schema().get("$defs").get("materialisationRegion");
        Set<String> allowed = names(region.get("properties"));
        for (MaterialisationSite site : SITES) {
            JsonNode step = written(site).get("through").get(0);
            JsonNode at = step.get("at");

            assertEquals("materialisation", step.get("kind").asString());
            assertTrue(allowed.containsAll(names(at)),
                    () -> site + " is written with a key the schema does not list: " + names(at));
            region.get("required").forEach(key -> assertTrue(at.has(key.asString()),
                    () -> site + " is written without " + key));
            assertTrue(words(region.get("properties").get("kind")).contains(at.get("kind").asString()),
                    () -> site + " is written with a kind the schema does not allow: " + at);
            if (at.has("slot")) {
                assertTrue(words(region.get("properties").get("slot"))
                        .contains(at.get("slot").asString()), () -> site + " has a slot the schema"
                        + " does not allow: " + at);
            }
        }
    }

    @Test
    void theStepsAreWrittenInTheOrderTheCopyWasMade() {
        JsonNode through = written(SITES.get(1)).get("through");

        assertEquals(2, through.size());
        assertEquals("materialisation", through.get(0).get("kind").asString());
        assertEquals("expansion", through.get(1).get("kind").asString());
    }

    @Test
    void anExpansionStepKeepsTheKeysItAlwaysHad() {
        JsonNode step = written(SITES.get(0)).get("through").get(1);

        assertEquals(Set.of("kind", "expanded", "module", "definition", "call", "lowered"),
                names(step));
    }
}
