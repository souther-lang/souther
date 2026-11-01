package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleCitation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every rule a compilation read has somewhere a report can send a reader, on a model that reads
 * rules of each kind a page is assembled for: the invariants of the types it takes, and a guard
 * that tells some of a position's values from the rest.
 */
class EveryRuleAModelsEvidenceReadHasAPlaceTest {

    private static final String WAITLIST = """
            module waitlist exposing ( Ticket, Party, Seated, seat )

            data Ticket = String
                invariant String.length(value) >= 1

            data Party = Int
                invariant value >= 1 && value <= 8

            data Seated = { ticket: Ticket, party: Party }

            behavior seat : (ticket: Ticket, party: Party)
                -> Seated | NotOnTheList | TooManyForOneTicket
                constructs Seated

            let seat (ticket, party) = {
                guard String.startsWith("w-", ticket.value) else NotOnTheList
                guard party.value <= 4 else TooManyForOneTicket
                Seated { ticket = ticket, party = party }
            }
            """;

    private static AdequacyReport.BehaviorReport seat() {
        Compilation compilation = Compilation.ofSource(WAITLIST, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        AdequacyReport.ModuleReport module = AdequacyReport.of(compilation).modules().getFirst();
        return module.behaviors().stream().filter(each -> each.name().equals("seat")).findFirst()
                .orElseThrow();
    }

    @Test
    void aPageIsAssembledWithEveryRuleItsMeasuresRead() {
        AdequacyReport.BehaviorReport behavior = seat();
        Set<RuleCitation.Written> read = new LinkedHashSet<>();
        for (RuleCitation each : behavior.evidence().ruleCitations()) {
            if (each instanceof RuleCitation.Written it) {
                read.add(it);
            }
        }
        assertTrue(behavior.rulePlaces().keySet().containsAll(read),
                () -> "every rule `seat`'s measures read has a place: " + read);
        assertTrue(!read.isEmpty(), "the model reads rules a page sends a reader to by place");
    }

    /** And the rule that divided a position is one of them. */
    @Test
    void includingTheOneThatDividedAPosition() {
        AdequacyReport.BehaviorReport behavior = seat();
        Set<RuleCitation.Written> divided = new LinkedHashSet<>();
        behavior.partition().axes().forEach(axis -> axis.divides().forEach(each -> {
            if (each.cited() instanceof RuleCitation.Written written) {
                divided.add(written);
            }
        }));
        assertTrue(!divided.isEmpty(),
                "the model carries a rule that divided a position by telling a set of its values"
                        + " from the rest");
        assertTrue(behavior.rulePlaces().keySet().containsAll(divided),
                () -> "the rule that divided a position has a place: " + divided);
    }
}
