package souther.compiler.meaning;

import java.util.Objects;

/**
 * The piece of a string that one statement about some piece is about.
 *
 * <p>Two statements about some piece are about the same piece only where they are the same
 * statement. How many statements deep one is read inside others ({@code depth}) tells nested ones
 * apart and says nothing of two that follow each other at the same depth, so it is not what a
 * piece is told apart by; the statement is ({@code site}), the place the quantifier over the
 * pieces stands at. Statements read at one site are about the one piece, and statements read at
 * two are about two, whichever string and window they are over.
 *
 * @param depth how many statements about some piece this one is read inside of
 * @param site  where the quantifier over the pieces stands, or empty where the piece is the one a
 *              statement about some piece would be about at that depth
 */
public record PieceWitness(int depth, String site) {

    public PieceWitness {
        if (depth < 0) {
            throw new IllegalArgumentException(
                    "a piece is of a statement some number of statements in: " + depth);
        }
        Objects.requireNonNull(site, "a statement stands somewhere, or nowhere in particular");
    }

    /** The piece of the statement at {@code site}, {@code depth} statements in. */
    public static PieceWitness of(int depth, String site) {
        return new PieceWitness(depth, site);
    }

    /** How it reads: its depth, and the statement where that tells it apart. */
    public String spelled() {
        return site.isEmpty() ? Integer.toString(depth) : depth + "@" + site;
    }

    @Override
    public String toString() {
        return spelled();
    }
}
