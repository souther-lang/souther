package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

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

    private static Map<String, PartitionEvidence> measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
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
}
