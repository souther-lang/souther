package souther.compiler.meaning;

import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;

import java.util.Objects;

/**
 * The piece of a string that one statement about some piece is about.
 *
 * <p>Two statements about some piece are about the same piece only where they are the same
 * statement. How many statements deep one is read inside others ({@code depth}) tells nested ones
 * apart and says nothing of two that follow each other at the same depth, so it is not what a
 * piece is told apart by; the statement is ({@code site}). Statements read at one site are about
 * the one piece, and statements read at two are about two, whichever string and window they are
 * over.
 *
 * @param depth how many statements about some piece this one is read inside of
 * @param site  which statement it is
 */
public record PieceWitness(int depth, Site site) {

    /** Which statement about some piece a piece is of. */
    public sealed interface Site {

        /** The piece the statement being read is about, as a quantifier over the pieces names it. */
        record Quantifier(ConstructOccurrence call) implements Site {

            public Quantifier {
                Objects.requireNonNull(call, "a quantifier is a call the source wrote");
            }
        }

        /**
         * The piece a closure parameter stands for, where no quantifier over the pieces is being
         * read: every statement about that piece names the parameter.
         */
        record Parameter(BindingId binding) implements Site {

            public Parameter {
                Objects.requireNonNull(binding, "a parameter is some binding");
            }
        }

        /** A piece nothing tells apart from the one a statement at that depth would be about. */
        record Unnamed() implements Site { }
    }

    public PieceWitness {
        if (depth < 0) {
            throw new IllegalArgumentException(
                    "a piece is of a statement some number of statements in: " + depth);
        }
        Objects.requireNonNull(site, "a statement stands somewhere, or nowhere in particular");
    }

    /** How it reads: its depth, and the statement where that tells it apart. */
    public String spelled() {
        return switch (site) {
            case Site.Quantifier quantifier -> depth + "@" + quantifier.call();
            case Site.Parameter parameter -> depth + "@" + parameter.binding();
            case Site.Unnamed _ -> Integer.toString(depth);
        };
    }

    @Override
    public String toString() {
        return spelled();
    }
}
