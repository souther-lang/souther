package souther.compiler.query;

import souther.compiler.partition.ObligationIdentity;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
    private final SequencedMap<String, List<OfferedRow>> rowsByBehavior;
    private final SequencedMap<String, Adequacy.Filling> searched;
    private final BorderAccount account;
    private final Set<ObligationIdentity> answered;
    private final Map<ObligationIdentity, Settlements.Shown> shownAt;

    /**
     * @param request  what was asked for, which is what settles which rows are here
     * @param rowsByBehavior one entry per behavior with rows to offer, in the order they were asked
     *                 about
     * @param searched what each behavior's own search came to, keyed the way a report keys them
     * @param account every point of a line this request answers for, whosever it is — a body's own
     *                 and its declarations' alike — or null where the request asked for no boundary
     *                 rows, which is not the same as a request that asked and found none
     * @param answered what the rows here settle: every item one of them would answer if it were
     *                 written, whichever row it was composed for
     * @param shownAt  the row a person is handed for each line and the input it stands at there,
     *                 for the lines one of these rows is offered for. Decided here because it is
     *                 decided by what is offered: the row composed for a line goes when another row
     *                 already answers it, so an input read off the search is one from before that
     *                 was settled
     */
    Offering(OfferingRequest request, SequencedMap<String, List<OfferedRow>> rowsByBehavior,
             SequencedMap<String, Adequacy.Filling> searched, BorderAccount account,
             Set<ObligationIdentity> answered,
             Map<ObligationIdentity, Settlements.Shown> shownAt) {
        this.shownAt = Collections.unmodifiableMap(new LinkedHashMap<>(shownAt));
        this.request = request;
        this.rowsByBehavior =
                Collections.unmodifiableSequencedMap(new LinkedHashMap<>(rowsByBehavior));
        this.searched = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(searched));
        this.account = account;
        this.answered = Collections.unmodifiableSet(new LinkedHashSet<>(answered));
    }

    /** What was asked for. */
    public OfferingRequest request() {
        return request;
    }

    /** The rows a person is handed, under the behavior each is written for. */
    public SequencedMap<String, List<OfferedRow>> rowsByBehavior() {
        return rowsByBehavior;
    }

    /** What each behavior's own search came to. */
    public SequencedMap<String, Adequacy.Filling> searched() {
        return searched;
    }

    /** Every point of a line this request answers for, whosever it is, or null where no boundary
     *  rows were asked for. */
    public BorderAccount account() {
        return account;
    }

    /** The items one of these rows would answer if it were written. */
    public Set<ObligationIdentity> answered() {
        return answered;
    }

    /**
     * The input of the row a person is handed for {@code item}'s line, or null where no row here is
     * offered for it — or where one is and stands at no input the line's reading names, as a row
     * at a point in a region does not. Which row it is, either way, is {@link #linesShownAt}'s.
     *
     * <p>The one place a report may name for such a line. What a search composed is a candidate and
     * what is left after the reduction is the work, and only the second of those is in front of a
     * person.
     */
    public InputOfARowForALine shownAt(ObligationIdentity item) {
        Settlements.Shown shown = shownAt.get(item);
        return shown == null ? null : shown.at().orElse(null);
    }

    /**
     * The lines {@code row} is the row a person is handed for, in the order they were asked about.
     *
     * <p>The same answer as {@link #shownAt}, asked from the row's side: a row standing at a line
     * is not composed for it — what a line is owed is answered in the account, and a row named for
     * whichever line it happened to be offered at would be renamed by an edit that did not touch it
     * — so this is how a block says over a row which lines it is for, without naming it after one.
     */
    public List<ObligationIdentity> linesShownAt(RowKey row) {
        List<ObligationIdentity> out = new ArrayList<>();
        shownAt.forEach((item, shown) -> {
            if (shown.rowKey().equals(row) && item instanceof ObligationIdentity.OfALine) {
                out.add(item);
            }
        });
        return List.copyOf(out);
    }

    /** How many pieces of work this offers, which is what a block says at the top of it. */
    public int count() {
        return rowsByBehavior.values().stream().mapToInt(List::size).sum();
    }
}
