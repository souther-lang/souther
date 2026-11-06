package souther.compiler.inputs;

/**
 * Which number of a position a reading was after, as far as that reading got.
 *
 * <p>Where a finding about a rule is filed, and what tells two of them at one path apart. A
 * {@code String} is measured more than one way — its own order, the length of it, and whatever else
 * an operation declares an account of — so a rule about one of them leaves that one short and the
 * others alone.
 *
 * <p><b>Two arms, and the line between them is how far the reading got.</b> Not whether the reading
 * stopped: a comparison the arithmetic could not take apart may still have named a term on one side
 * of it, and {@code String.length(s) > n * n} is filed at the length even though nothing read the
 * product. What each arm says is what this reader knows, which is the only thing it may say.
 *
 * <p><b>And an exact term is not a claim about the subject.</b> What a rule this compiler could not
 * read is <em>about</em> is the part that was not read; naming the term the walk was looking at
 * says where to look, and a reader may not turn it into what the rule divides. The two are separate
 * because a diagnostic position and a semantic subject travelled as one value before, and the first
 * was read as the second.
 *
 * <p>Carried as a boolean before — a path and whether a number was taken of it. That was the shape
 * of what one producer could supply rather than of what a coordinate is, and it was already too
 * narrow the day it was written: a term taken of a position is taken <em>by an operation</em>, and
 * two operations over one path are two coordinates a report has to tell apart.
 */
public sealed interface FilingCoordinate {

    /** Where in the value it sits, which both arms can always say. */
    TermPath path();

    /**
     * The number itself, where the reading named it.
     *
     * <p>Every reader that reached the canonical quantity has one, and so does one that named a
     * term on a side of a comparison it could not read as a whole. The operation a taken number is
     * taken by is part of the term and is never worked out again here.
     */
    record OfTerm(NumericTerm term) implements FilingCoordinate {

        public OfTerm {
            if (term == null) {
                throw new IllegalArgumentException("a coordinate that names a number names one");
            }
        }

        @Override
        public TermPath path() {
            return term.subjectPath();
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    /**
     * The position and no more, where the reading did not get as far as a number.
     *
     * <p>A position the walk met inside something it could not take apart. Filed here rather than
     * guessed at: which number of the position such a rule is about is what was not read, and a
     * term made up for it would be this compiler naming an operation the model never wrote.
     */
    record AtPosition(TermPath path) implements FilingCoordinate {

        public AtPosition {
            if (path == null) {
                throw new IllegalArgumentException("a coordinate sits somewhere in the value");
            }
        }

        @Override
        public String toString() {
            return path.toString();
        }
    }

    /** The number, for a reader that named one. */
    static FilingCoordinate of(NumericTerm term) {
        return new OfTerm(term);
    }

    /** The position, for a reader that did not. */
    static FilingCoordinate at(TermPath path) {
        return new AtPosition(path);
    }
}
