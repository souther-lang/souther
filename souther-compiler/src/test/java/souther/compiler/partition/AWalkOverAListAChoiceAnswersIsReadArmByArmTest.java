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
        return screened("", codes);
    }

    /** The same, with {@code before} worked out ahead of the screening. */
    private static PartitionEvidence screened(String before, String codes) {
        return screened(before, codes, "1");
    }

    /** The same, asking for at least {@code found} of what the join found. */
    private static PartitionEvidence screened(String before, String codes, String found) {
        return screenedBy(before, codes, "List.length(found) >= " + found);
    }

    /** The same, the guard on what the join found being {@code condition}. */
    private static PartitionEvidence screenedBy(String before, String codes, String condition) {
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
                    %s
                    let codes = %s
                    let found = List.flatMap(e -> List.filter(c -> c.code == e, contacts), codes)
                    guard %s else NoMatch
                    Matched { ids = List.map(c -> c.id, found) }
                }
                """.formatted(before, codes, condition);
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

    /**
     * A comparison inside a closure is reached only past what the run works out before the call
     * applies the closure: the numbers from nought to the lead's code are more than a list holds
     * where the code is past what a list holds, so no run with such a code gets to the screening,
     * and the code is not shown to be compared at every value. Without them it is.
     */
    @Test
    void aComparisonInAClosureIsReachedOnlyPastWhatTheRunWorksOutBeforeIt() {
        PartitionEvidence padded = screened("let pad = List.rangeInclusive(0, lead.code)",
                "[ lead.code ]");
        assertEquals(List.of("contacts[*].code", "lead.code"),
                notReachedAtEveryValue(padded), () -> padded.notRead().toString());
        PartitionEvidence one = screened("", "[ lead.code ]");
        assertEquals(List.of(), stopped(one), () -> one.notRead().toString());
    }

    /**
     * The witness a join is shown to fit on holds as few contacts as the way lets it: a guard
     * asking for two at least leaves one of two, which fits. One asking for as many as a list
     * holds leaves that many, and two codes keeping them all join past what a list holds. A guard
     * asking anything else of how many there are leaves no list cut down to so few a row of the
     * way.
     */
    @Test
    void theWitnessAJoinFitsOnHoldsAsFewAsTheWayLetsIt() {
        PartitionEvidence two = screened("guard List.length(contacts) >= 2 else NoMatch",
                "[ lead.code ]");
        assertEquals(List.of(), notReachedAtEveryValue(two), () -> two.notRead().toString());
        PartitionEvidence full = screened(
                "guard List.length(contacts) >= 2147483647 else NoMatch",
                "[ lead.code, lead.code ]");
        assertEquals(List.of("contacts[*].code", "lead.code"), notReachedAtEveryValue(full),
                () -> full.notRead().toString());
        PartitionEvidence atMost = screened("guard List.length(contacts) <= 3 else NoMatch",
                "[ lead.code ]");
        assertEquals(List.of("contacts[*].code", "lead.code"), notReachedAtEveryValue(atMost),
                () -> atMost.notRead().toString());
    }

    /** Where a relation was read and a run may stop on the way to it. */
    private static List<String> notReachedAtEveryValue(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
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

    /**
     * The guard on how many were found is a line at one, where the list the join makes has a
     * place, so the join is not one a row of the line stops at and nothing is left unread. A guard
     * asking for as many as a list holds is not read as a relation between the inputs: it is
     * said to be about what a run comes to.
     */
    @Test
    void aGuardCountingAJoinIsReadWhereTheCountIsOneAListHolds() {
        PartitionEvidence few = screened("", "[ lead.code ]", "1");
        assertEquals(List.of(), stopped(few), () -> few.notRead().toString());
        assertEquals(List.of(), aboutARun(few), () -> few.notRead().toString());
        PartitionEvidence all = screened("", "[ lead.code ]", "2147483647");
        assertEquals(List.of("contacts[*].code", "lead.code"), aboutARun(all),
                () -> all.notRead().toString());
    }

    /**
     * The line is the one the whole comparison draws on the count, not a number written beside
     * it: the same line at one is read however it is written. A count the line moves with the
     * input on is no line at a count a list holds, and its list is not taken to be made.
     */
    @Test
    void theLineIsTheOneTheComparisonDrawsOnTheCount() {
        for (String atOne : List.of("List.length(found) >= 1", "List.length(found) - 1 >= 0",
                "2 * List.length(found) >= 2", "1 <= List.length(found)")) {
            PartitionEvidence read = screenedBy("", "[ lead.code ]", atOne);
            assertEquals(List.of(), stopped(read), () -> atOne + read.notRead());
            assertEquals(List.of(), aboutARun(read), () -> atOne + read.notRead());
        }
        String movesWithTheInput = "List.length(found) >= lead.code";
        PartitionEvidence moves = screenedBy("", "[ lead.code ]", movesWithTheInput);
        assertEquals(List.of("contacts[*].code", "lead.code"), stopped(moves),
                () -> moves.notRead().toString());
    }

    /**
     * A line below nought is at no count a list holds, however a number beside the count is
     * written: {@code List.length(found) + 100 >= 1} holds for every list, and the rule cuts
     * nothing rather than being read at a list that has no place.
     */
    @Test
    void aLineBelowNoughtIsAtNoCountAListHolds() {
        for (String below : List.of("List.length(found) + 100 >= 1",
                "List.length(found) + 1 >= 0")) {
            PartitionEvidence evidence = screenedBy("", "[ lead.code ]", below);
            assertEquals(List.of(), stopped(evidence), () -> below + evidence.notRead());
            assertTrue(evidence.notRead().stream().anyMatch(each -> each.reason()
                    == UndividedPosition.Reason.RULE_CUTS_NOTHING), () -> evidence.notRead().toString());
        }
    }

    /** Where what the rule states is about a run that may stop on the way to it. */
    private static List<String> aboutARun(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason() == UndividedPosition.Reason.RULE_ABOUT_A_RUN)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
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
