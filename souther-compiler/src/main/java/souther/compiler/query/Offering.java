package souther.compiler.query;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.SequencedMap;

/**
 * The rows one run hands a person, under the behavior each is written for.
 *
 * <p>What is left of a {@link Composition} once what each row would settle has been asked: a row
 * answering only what another row here answers is not one of these. So this is what a block is
 * written from, and there is no way to write one from the rows before that question was put — which
 * there was while both were one type, and a renderer that reached for the wrong one printed work
 * nobody had chosen.
 *
 * <p>Nothing here is evidence of coverage. A row this holds is a question — these inputs, and what
 * does the system answer? — and what it would settle if it were written is not something this says
 * about the file.
 *
 * <p>And what the two searches came to beside the rows they composed, which is the other half of
 * what a person is owed: a block that printed only what it managed would read as though it had
 * filled everything.
 *
 * @param request  what was asked for, which is what settles which rows are here
 * @param rows     one entry per behavior with rows to offer, in the order they were asked about
 * @param searched what each behavior's own search came to, keyed the way a report keys them
 * @param declared what the module's declarations are owed, or null where the request asked for no
 *                 boundary rows — which is not the same as a request that asked and found none
 * @param answered what the rows here settle: every item one of them would answer if it were
 *                 written, whichever row it was composed for. Empty where nobody put the question,
 *                 which is what {@link Composition#offeringEverything()} hands back
 */
public record Offering(OfferingRequest request, SequencedMap<String, List<OfferedRow>> rows,
                       SequencedMap<String, Adequacy.Filling> searched, DeclaredRows declared,
                       Set<OfferItem> answered) {

    public Offering {
        rows = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(rows));
        searched = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(searched));
        answered = Collections.unmodifiableSet(new LinkedHashSet<>(answered));
    }

    /** How many pieces of work this offers, which is what a block says at the top of it. */
    public int count() {
        return rows.values().stream().mapToInt(List::size).sum();
    }
}
