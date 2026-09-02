package souther.compiler.publish;

import souther.compiler.observe.Incompleteness;

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
public record PublishedIncompleteness(Incompleteness.Fact fact, Optional<PublishedAt> at) {

    public PublishedIncompleteness {
        if (fact == null) {
            throw new IllegalArgumentException("an entry says what could not be read");
        }
        at = at == null ? Optional.empty() : at;
    }
}
