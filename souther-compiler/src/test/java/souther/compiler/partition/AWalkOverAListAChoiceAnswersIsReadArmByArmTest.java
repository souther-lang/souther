package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a walk over a list an {@code if} or a {@code match} chose is read as the same
 * walk over the list a filter keeps is: each element of each arm, kept where its arm is taken.
 */
class AWalkOverAListAChoiceAnswersIsReadArmByArmTest {

    private static final String MODULE = "probe";

    private static PartitionEvidence screened(String codes) {
        String model = """
                module probe

                data Email = { code: Int }
                data Phone = { number: Int }
                data Point = Email | Phone

                data Lead = { code: Int, known: Bool, point: Point }
                data Contact = { id: Int, code: Int }

                data NoMatch
                data Matched = { ids: List<Int> }

                behavior screen : (lead: Lead, contacts: List<Contact>) -> NoMatch | Matched

                let screen (lead, contacts) = {
                    let codes = %s
                    let found = List.flatMap(e -> List.filter(c -> c.code == e, contacts), codes)
                    guard List.length(found) >= 1 else NoMatch
                    Matched { ids = List.map(c -> c.id, found) }
                }
                """.formatted(codes);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence screen = compilation.db()
                .ask(new Adequacy.Coverage(MODULE)).value().get("screen");
        assertNotNull(screen, "the model under test compiles");
        return screen;
    }

    /** Where a reading of a rule stopped, as against one read to the end that drew no line. */
    private static List<String> stopped(PartitionEvidence evidence) {
        return evidence.notRead().stream().filter(PartitionEvidence.NotRead::readingStopped)
                .map(PartitionEvidence.NotRead::at).toList();
    }

    /** The filter that keeps the one code where the lead is known, which is read already. */
    @Test
    void theSameListAFilterKeepsIsRead() {
        PartitionEvidence evidence = screened("List.filter(k -> lead.known, [ lead.code ])");

        assertEquals(List.of(), stopped(evidence), () -> evidence.notRead().toString());
    }

    @Test
    void aListAnIfChoosesIsRead() {
        PartitionEvidence evidence = screened("if lead.known then [ lead.code ] else []");

        assertEquals(List.of(), stopped(evidence), () -> evidence.notRead().toString());
    }

    /** A value an arm binds is read where the arm is entered. */
    @Test
    void aListAMatchChoosesIsReadWithWhatEachArmBinds() {
        PartitionEvidence evidence = screened(
                "match lead.point with | Email as m -> [ m.code ] | Phone -> []");

        assertEquals(List.of(), stopped(evidence), () -> evidence.notRead().toString());
    }

    /** One arm this cannot write out leaves the whole unwritten, and the walk over it unread. */
    @Test
    void anArmThatCannotBeWrittenOutLeavesTheWalkUnread() {
        PartitionEvidence evidence = screened(
                "if lead.known then [ lead.code ] else List.append([ lead.code ], [ lead.code ])");

        assertTrue(stopped(evidence).contains("contacts[*].code"),
                () -> evidence.notRead().toString());
    }
}
