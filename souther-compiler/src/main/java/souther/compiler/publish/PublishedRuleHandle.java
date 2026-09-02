package souther.compiler.publish;

import souther.compiler.check.RuleCitation;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;

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
public record PublishedRuleHandle(Optional<String> name, Where where, Place at,
                                  Optional<String> reachedBy)
        implements Comparable<PublishedRuleHandle> {

    /**
     * Where a report says the rule is, as it says it.
     *
     * <p>Three and not two. A place in a file this compile holds is what a reader can be sent to;
     * a position in a text it cannot name is still printed, line and column, because whoever is
     * showing the report knows which text it is; and code out of sight has no position at all.
     *
     * <p>Not {@link PublishedAt} alone, which is the shape the document's own {@code at} field
     * takes and so has nothing for the middle one. Borrowed for this, two rules the report prints
     * at different lines of an unnamed text came out as one value — and the choice between them
     * fell back to whichever the set of them iterated first.
     */
    public sealed interface Place extends Comparable<Place> {

        /** In a file this compile holds, so a reader can be sent to it. */
        record InSource(PublishedAt at) implements Place {}

        /** In a text this compilation cannot name: the numbers are real and the file is the
         *  reader's to know. */
        record Unplaced(int line, int column) implements Place {}

        /** No position at all, which is what a report says of code out of sight. */
        record Nowhere() implements Place {}

        /** A place a reader can be sent to first, then one only whoever is showing the report can
         *  use, and last none — which is how much a reader is given, most first. */
        private int rank() {
            return switch (this) {
                case InSource _ -> 0;
                case Unplaced _ -> 1;
                case Nowhere _ -> 2;
            };
        }

        @Override
        default int compareTo(Place other) {
            int kind = Integer.compare(rank(), other.rank());
            if (kind != 0) {
                return kind;
            }
            return switch (this) {
                case InSource it ->
                        PublicationOrders.PLACES.compare(it.at(), ((InSource) other).at());
                case Unplaced it -> {
                    Unplaced also = (Unplaced) other;
                    int line = Integer.compare(it.line(), also.line());
                    yield line != 0 ? line : Integer.compare(it.column(), also.column());
                }
                case Nowhere _ -> 0;
            };
        }
    }

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
        if (where == null || at == null) {
            throw new IllegalArgumentException("a rule is reached one of three ways");
        }
        name = name == null ? Optional.empty() : name;
        reachedBy = reachedBy == null ? Optional.empty() : reachedBy;
    }

    /** How a document would write {@code cited}. */
    public static PublishedRuleHandle of(RuleCitation cited) {
        return switch (cited) {
            case RuleCitation.Named it ->
                    new PublishedRuleHandle(Optional.of(it.name()), Where.NAMED,
                            new Place.Nowhere(), Optional.empty());
            case RuleCitation.WrittenAt it -> new PublishedRuleHandle(Optional.empty(),
                    it.at() instanceof Citation.Elsewhere ? Where.ELSEWHERE : Where.WRITTEN,
                    placeOf(it.at()),
                    it.at() instanceof Citation.Elsewhere out
                            ? Optional.of(out.provenance().reachedBy()) : Optional.empty());
        };
    }

    /**
     * Where a report says that code is: the place a reader can be sent to where there is one, and
     * otherwise the numbers it prints instead.
     *
     * <p>The numbers are asked of the citation and not of the place, because a place is what the
     * document's own field is made of and there is none for a position in a text this compilation
     * cannot name — while the sentence about the rule prints one all the same.
     */
    private static Place placeOf(Citation cited) {
        Optional<PublishedAt> held = PublishedAt.of(cited);
        if (held.isPresent()) {
            return new Place.InSource(held.get());
        }
        SourcePos where = switch (cited) {
            case Citation.Written it -> it.at();
            case Citation.Unplaced it -> it.at();
            case Citation.Reached it -> it.at();
            case Citation.UnplacedElsewhere it -> it.at();
            case Citation.OutOfSight _ -> null;
        };
        return where == null ? new Place.Nowhere()
                : new Place.Unplaced(where.line(), where.column());
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
        int kind = Integer.compare(rank(where), rank(other.where));
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
        return at.compareTo(other.at);
    }

    /** Which of the three kinds of sentence comes first, written out rather than read off how the
     *  constants happen to be declared. */
    private static int rank(Where where) {
        return switch (where) {
            case NAMED -> 0;
            case WRITTEN -> 1;
            case ELSEWHERE -> 2;
        };
    }
}
