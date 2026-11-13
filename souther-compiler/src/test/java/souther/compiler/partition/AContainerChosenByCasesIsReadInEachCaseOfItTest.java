package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A container an operation of the library is handed may be chosen by the cases of a value:
 * {@code Set.contains(p, campaignsOf(lead))} where {@code campaignsOf} is a {@code match}. The law
 * of the operation is read over the container in each case, and the call stands where the value is
 * the case taken. A model is measured whatever the cases are, whether each holds a field of its
 * own or they share one.
 */
class AContainerChosenByCasesIsReadInEachCaseOfItTest {

    private static final String SEPARATE = """
            module probe
            data NewLead = { campaigns: Set<String> }
            data WorkingLead = { campaigns: Set<String>, touches: Int }
            data OpenLead = NewLead | WorkingLead

            let campaignsOf (lead: OpenLead): Set<String> =
                match lead with
                    | NewLead { campaigns } -> campaigns
                    | WorkingLead { campaigns } -> campaigns

            behavior listed : (lead: OpenLead, priority: String) -> Int
            let listed (lead, priority) =
                if Set.contains(priority, campaignsOf(lead)) then 25 else 0
            """;

    /** The cases share the field by a spread, which a path cannot tell from one value. */
    private static final String SHARED = """
            module probe
            data Common = { campaigns: Set<String> }
            data NewLead = { ...Common }
            data WorkingLead = { ...Common, touches: Int }
            data OpenLead = NewLead | WorkingLead

            let campaignsOf (lead: OpenLead): Set<String> =
                match lead with
                    | NewLead { campaigns } -> campaigns
                    | WorkingLead { campaigns } -> campaigns

            behavior listed : (lead: OpenLead, priority: String) -> Int
            let listed (lead, priority) =
                if Set.contains(priority, campaignsOf(lead)) then 25 else 0
            """;

    /** A third case the match answers false at: its arm folds away, and what is left is two arms
     *  that do not cover the value. */
    private static final String NOT_EVERY_CASE = """
            module probe
            data NewLead = { campaigns: Set<String> }
            data WorkingLead = { campaigns: Set<String>, touches: Int }
            data ClosedLead = { reason: String }
            data Lead = NewLead | WorkingLead | ClosedLead

            behavior listed : (lead: Lead, priority: String) -> Bool
            let listed (lead, priority) =
                match lead with
                    | NewLead { campaigns } -> Set.contains(priority, campaigns)
                    | WorkingLead { campaigns } -> Set.contains(priority, campaigns)
                    | ClosedLead -> false
            """;

    /** The same relation chosen by a flag the model writes, which is no choice by cases. */
    private static final String BY_A_FLAG = """
            module probe
            data Lead = { fresh: Bool, campaigns: Set<String>, others: Set<String> }

            behavior listed : (lead: Lead, priority: String) -> Bool
            let listed (lead, priority) =
                (lead.fresh && Set.contains(priority, lead.campaigns))
                    || (Bool.not(lead.fresh) && Set.contains(priority, lead.others))
            """;

    private static Map<String, PartitionEvidence> measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        Map<String, PartitionEvidence> out =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        assertNotNull(out, "the model under test compiles");
        return out;
    }

    @Test
    void aModelWhoseCasesEachHoldTheContainerIsMeasured() {
        assertNotNull(measured(SEPARATE).get("listed"));
        assertNotNull(measured(SHARED).get("listed"));
    }

    /**
     * What a statement leaves unread does not depend on whether the arms cover every case of the
     * value: the relation of an arm stands only under its cases, whichever way the rest is
     * written. A choice by a flag is no choice by cases and is read as the one statement it is,
     * which leaves more unread and is never read as arms.
     */
    @Test
    void whatIsLeftUnreadIsTheSameWhetherTheArmsCoverEveryCaseAndWhetherTheChoiceIsByCases() {
        Map<String, List<UndividedPosition.Reason>> reasons = new LinkedHashMap<>();
        Map<String, String> models = new LinkedHashMap<>();
        models.put("everyCase", SEPARATE);
        models.put("notEveryCase", NOT_EVERY_CASE);
        models.put("byAFlag", BY_A_FLAG);
        models.forEach((name, model) -> reasons.put(name,
                measured(model).get("listed").notRead().stream()
                        .map(PartitionEvidence.NotRead::reason).distinct().toList()));
        assertEquals(Map.of(
                "everyCase", List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                "notEveryCase", List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                "byAFlag", List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                        UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE)),
                reasons);
    }

    /**
     * The container is whichever of the cases the value is, and {@code Set.contains} relates the
     * priority to that one: the same relation of two values it states of a container written
     * out, at the place of each case's field. Nothing of what it relates is left unread, whether
     * the cases hold a field each or share one.
     */
    @Test
    void aValueRelatedToTheContainerOfWhicheverCaseIsTakenIsReadAsRelatedToIt() {
        for (String model : List.of(SEPARATE, SHARED)) {
            List<UndividedPosition.Reason> left = measured(model).get("listed").notRead().stream()
                    .map(PartitionEvidence.NotRead::reason)
                    .distinct()
                    .toList();
            assertEquals(List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES), left, model);
        }
    }
}
