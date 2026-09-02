package souther.compiler.publish;

import souther.compiler.check.RuleCitation;
import souther.compiler.diag.Citation;

import java.util.Optional;

/**
 * How a document sends a reader to a rule, as the things a document's words for it are made of.
 *
 * <p>The projection of a {@link RuleCitation} onto what varies in the sentence a report writes:
 * the name where the author gave one, and otherwise whether the code is here or reached from here,
 * where it is, and what it is reached by. Everything else a citation carries is how this compiler
 * came to be holding it.
 *
 * <p><b>Made so that two handles a document writes alike are one value.</b> Choosing one of several
 * takes a comparison, and a comparison over what a citation is rather than over what is written of
 * it can come out equal for two handles a reader can tell apart — and then which is written is
 * whichever the set of them happened to iterate first, which is the thing this whole change exists
 * to have removed.
 *
 * <p>So this and never {@link RuleCitation} is what the order is over. Two citations that project
 * here alike are two a reader cannot tell apart, and which of those a document writes is not a
 * question about the document.
 */
public record PublishedRuleHandle(Optional<String> name, Where where, Optional<PublishedAt> at,
                                  Optional<String> reachedBy)
        implements Comparable<PublishedRuleHandle> {

    /** Which of the three kinds of sentence a report writes for a rule. */
    public enum Where {

        /** The author gave it a name, and that is what a reader is told. */
        NAMED,

        /** It has no name and is written where a reader can be sent. */
        WRITTEN,

        /** It has no name and the code is out of sight, so what is said is where it came from. */
        ELSEWHERE
    }

    public PublishedRuleHandle {
        if (where == null) {
            throw new IllegalArgumentException("a rule is reached one of three ways");
        }
        name = name == null ? Optional.empty() : name;
        at = at == null ? Optional.empty() : at;
        reachedBy = reachedBy == null ? Optional.empty() : reachedBy;
    }

    /** How a document would write {@code cited}. */
    public static PublishedRuleHandle of(RuleCitation cited) {
        return switch (cited) {
            case RuleCitation.Named it ->
                    new PublishedRuleHandle(Optional.of(it.name()), Where.NAMED,
                            Optional.empty(), Optional.empty());
            case RuleCitation.WrittenAt it -> new PublishedRuleHandle(Optional.empty(),
                    it.at() instanceof Citation.Elsewhere ? Where.ELSEWHERE : Where.WRITTEN,
                    PublishedAt.of(it.at()),
                    it.at() instanceof Citation.Elsewhere out
                            ? Optional.of(out.provenance().reachedBy()) : Optional.empty());
        };
    }

    /**
     * Which of two a document writes first: a name the author gave before a place they did not,
     * a place before code out of sight, and two of one kind by where they are and what they say.
     *
     * <p>A rank and not a ranking: what it is for is that a run choosing between the same two
     * chooses the same way, and a reader given a name has the word the model uses where a reader
     * given a place has what there is instead.
     */
    @Override
    public int compareTo(PublishedRuleHandle other) {
        int kind = Integer.compare(where.ordinal(), other.where.ordinal());
        if (kind != 0) {
            return kind;
        }
        int named = name.orElse("").compareTo(other.name.orElse(""));
        if (named != 0) {
            return named;
        }
        int reached = reachedBy.orElse("").compareTo(other.reachedBy.orElse(""));
        if (reached != 0) {
            return reached;
        }
        if (at.isPresent() && other.at.isPresent()) {
            return PublicationOrders.PLACES.compare(at.get(), other.at.get());
        }
        return Boolean.compare(at.isPresent(), other.at.isPresent());
    }
}
