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
 * <p><b>Made in one place.</b> A class rather than a record, so that the way to hold one is to have
 * asked: {@link Composition#keeping} is in this package and nothing outside it can write the
 * constructor. A record would publish the constructor with the type, and the sentence above — that
 * a renderer cannot be handed rows nobody chose — would be a thing to remember rather than a thing
 * that holds.
 */
public final class Offering {

    private final OfferingRequest request;
    private final SequencedMap<String, List<OfferedRow>> rows;
    private final SequencedMap<String, Adequacy.Filling> searched;
    private final BorderAccount declared;
    private final Set<OfferItem> answered;

    /**
     * @param request  what was asked for, which is what settles which rows are here
     * @param rows     one entry per behavior with rows to offer, in the order they were asked about
     * @param searched what each behavior's own search came to, keyed the way a report keys them
     * @param declared what the module's declarations are owed, or null where the request asked for
     *                 no boundary rows — which is not the same as a request that asked and found
     *                 none
     * @param answered what the rows here settle: every item one of them would answer if it were
     *                 written, whichever row it was composed for
     */
    Offering(OfferingRequest request, SequencedMap<String, List<OfferedRow>> rows,
             SequencedMap<String, Adequacy.Filling> searched, BorderAccount declared,
             Set<OfferItem> answered) {
        this.request = request;
        this.rows = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(rows));
        this.searched = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(searched));
        this.declared = declared;
        this.answered = Collections.unmodifiableSet(new LinkedHashSet<>(answered));
    }

    /** What was asked for. */
    public OfferingRequest request() {
        return request;
    }

    /** The rows a person is handed, under the behavior each is written for. */
    public SequencedMap<String, List<OfferedRow>> rows() {
        return rows;
    }

    /** What each behavior's own search came to. */
    public SequencedMap<String, Adequacy.Filling> searched() {
        return searched;
    }

    /** What the module's declarations are owed, or null where none were asked for. */
    public BorderAccount declared() {
        return declared;
    }

    /** The items one of these rows would answer if it were written. */
    public Set<OfferItem> answered() {
        return answered;
    }

    /** How many pieces of work this offers, which is what a block says at the top of it. */
    public int count() {
        return rows.values().stream().mapToInt(List::size).sum();
    }
}
