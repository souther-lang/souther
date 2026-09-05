package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.RuleRef;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeKey;
import souther.compiler.types.WrittenOwner;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every kind of rule a document can name is one it can write down and one it has a word for.
 *
 * <p>Two total answers over {@link RuleRef}, and neither is total by anything the compiler checks.
 * They are switches with a throwing arm, so a kind added to the seal keeps compiling and stops the
 * first document that names one — at whichever build first writes a model with that kind of rule in
 * it, which is nobody's test and everybody's build.
 *
 * <p>That has happened. A rule about the strings at a position was added to the seal with both arms
 * left refusing, on the reasoning that nothing published one yet; the day something did, generating
 * an adequacy report threw. The refusal was right when it was written and wrong the moment the
 * reader existed, and nothing here connected the two.
 *
 * <p>So the population comes from the seal and every member is asked both questions. A kind added
 * without an answer fails here rather than in a build somebody else is running.
 */
class EveryKindOfRuleADocumentCanNameHasAnIdentityAndAWordTest {

    /**
     * One of each kind, built by hand.
     *
     * <p>From the seal and not from a compilation: what is being asked is whether every kind has an
     * answer, and a model that happens to write four kinds of rule would make the population what
     * that model states. A kind nothing can yet produce is a kind a document may still be asked to
     * name the day something produces one, which is exactly the case this exists for.
     */
    private static List<RuleRef> everyKind() {
        WrittenOwner.Body body = new WrittenOwner.Body("m", "b");
        SourceConstructOrigin written =
                new SourceConstructOrigin(body, 1, 0, SourceConstruct.BINARY);
        Clause.Ref clause = new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("m", "Amount")), 0),
                Optional.of(new ClauseName("cap")));
        return List.of(
                new RuleRef.Invariant(clause),
                new RuleRef.Ensures(
                        new BehaviorContract.RuleId(new ValueName.Behavior("m", "b"), 0, 0, null),
                        "c"),
                new RuleRef.Comparison("b", written),
                new RuleRef.Predicate("b", new SourceConstructOrigin(body, 2, 0,
                        SourceConstruct.CALL)));
    }

    /** That the list above is the seal and not a list somebody kept up by hand. */
    @Test
    void thePopulationIsEveryKindTheSealHas() {
        assertEquals(
                Set.copyOf(RuleRef.class.getPermittedSubclasses() == null ? List.of()
                        : List.of(RuleRef.class.getPermittedSubclasses())),
                everyKind().stream().map(each -> (Class<?>) each.getClass())
                        .collect(Collectors.toSet()),
                "one of each kind of rule the seal has, and no other");
    }

    @Test
    void everyKindCanBeWrittenDown() {
        for (RuleRef each : everyKind()) {
            ObjectNode into = JsonMapper.builder().build().createObjectNode();
            AdequacyReport.ruleId(into, each);
            assertTrue(into.has("kind"),
                    "a document says which kind of rule it is naming: " + each);
        }
    }

    @Test
    void everyKindHasAWordForItsKind() {
        for (RuleRef each : everyKind()) {
            assertTrue(!AdequacyReport.schemaRuleKind(each).isBlank(),
                    "a document has a word for this kind of rule: " + each);
        }
    }

    /** And the words tell the kinds apart, which is what a reader groups by. */
    @Test
    void andTheWordsTellTheKindsApart() {
        List<String> words = everyKind().stream()
                .map(AdequacyReport::schemaRuleKind).toList();

        assertEquals(words.size(), Set.copyOf(words).size(),
                "each kind is written under a word of its own: " + words);
    }
}
