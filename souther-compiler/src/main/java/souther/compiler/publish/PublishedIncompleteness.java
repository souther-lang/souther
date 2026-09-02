package souther.compiler.publish;

import souther.compiler.observe.Incompleteness;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

/**
 * One entry of what a document says a module could not read, as the document writes it.
 *
 * <p>The fact, and the one place a reader is sent to for it. Everything the schema has room for
 * follows from those two — what happened and what it happened to are the fact's, and where to look
 * is what a set of citations comes to once one of them has been chosen.
 *
 * <p><b>Here so that the order is over what is written.</b> A key over the account's own values
 * would be free to leave out something a reader can see, and the two entries it could not tell
 * apart would be written in the order a walk met them. Written out of this, the key is over the
 * whole of what the entry is.
 *
 * <p>The source of the fact is named and not resolved. What a document calls a source is recorded
 * as the document writes it, so resolving one here would make the choosing of an order decide which
 * sources a document goes on to explain.
 */
public record PublishedIncompleteness(Incompleteness.Fact fact, Optional<PublishedAt> at,
                                      boolean metWhereNothingCanBeWritten) {

    public PublishedIncompleteness {
        if (fact == null) {
            throw new IllegalArgumentException("an entry says what could not be read");
        }
        at = at == null ? Optional.empty() : at;
    }

    /**
     * What a module could not read, as the entries a document writes, in the order it writes them.
     *
     * <p>The one way to have these. Three surfaces say them — the document a build reads, the page
     * a person reads, and the block a generator writes — and each of the three would otherwise take
     * the account's own set and publish whatever it iterated in, which is how two of them came to
     * disagree with the third. Made once here, there is no set for a surface to walk.
     *
     * <p>The place for each is chosen out of everywhere the fact was met, and the choosing happens
     * before anything is written: recording a source is what a document does while writing, so a
     * comparison asked at that point would let the sorting decide which sources a document goes on
     * to explain.
     *
     * <p>A fact met nowhere a reader can be sent comes out with no place. Whether that is something
     * to refuse is the surface's: the page a person reads and the block a generator writes say
     * these facts without pointing anywhere, and only the document has a field that a place is
     * missing from ({@link NoPlaceToWrite}). Refused here, a generation stopped because a report it
     * was not writing would have had a field to fill.
     */
    public static CanonicalArrangement<PublishedIncompleteness> everyOne(
            Collection<Incompleteness.Met> gaps) {
        List<PublishedIncompleteness> out = new ArrayList<>(gaps.size());
        for (Incompleteness.Met gap : gaps) {
            Optional<PublishedAt> place = PublicationOrders.placeFor(gap.citations());
            out.add(new PublishedIncompleteness(gap.fact(), place,
                    place.isEmpty() && !gap.citations().isEmpty()));
        }
        return PublicationOrders.WHAT_WENT_UNREAD.arrange(out);
    }
}
