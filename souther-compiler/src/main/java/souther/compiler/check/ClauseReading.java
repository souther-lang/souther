package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;

/**
 * A clause tree read into one state, the connectives being the same whatever the leaves are read as.
 *
 * <p>What a clause is written out of — a conjunction, a choice, a denial — is the clause's own shape
 * and not a fact about the language it is read in. Written once per language, that shape is the same
 * code as many times as there are languages, and each copy is free to drift from the others.
 *
 * <p><b>And the connectives belong to the clause and not to a component of the state.</b> That is
 * what this is for. A choice between two alternatives is a choice between two <em>readings of the
 * whole value</em>, so the alternative that cannot be taken has to be dropped by asking the whole of
 * what is known about it. Applied inside each language on its own, an alternative was dropped only
 * where the language doing the joining was also the one that could show it impossible — and a choice
 * between a branch no order admits and a branch no set of values admits came out open, each language
 * having found nothing wrong with the branch the other one refused.
 *
 * @param <S> what a reading of a clause comes to
 */
interface ClauseReading<S> {

    /** What a clause this reading has no word for leaves, which is everything it had. */
    S nothingSaid();

    /**
     * What one clause of no connective says, stated where {@code positive} and denied where it is
     * not.
     *
     * <p>Reached with the denials already counted, so a reading of a comparison is a reading of the
     * comparison it states rather than of the one that was written.
     */
    S leaf(Core e, boolean positive);

    /** Both readings holding at once. */
    S both(S one, S other);

    /** Either reading holding. */
    S either(S one, S other);

    /**
     * What {@code e} leaves, stated where {@code positive} and denied where it is not.
     *
     * <p>A denial is carried to the leaves rather than applied to what a branch came to. What a
     * state says is a fact per position, and the denial of that is not one — the values a
     * conjunction rules out are a choice between the positions it named, which no map of positions
     * holds. Carried down, every denial meets a leaf, where it is one.
     */
    default S read(Core e, boolean positive) {
        return read(e, positive, null);
    }

    /**
     * The same, telling {@code per} what each part of the clause came to as it is read.
     *
     * <p>Keyed by the part as the tree holds it, so a reader that walks the same clause afterwards
     * finds what this reading made of the very node it is looking at. Asked again instead, that
     * reader is a second reading of the part, and two readings of one conjunct agree only for as
     * long as nobody changes one of them.
     */
    default S read(Core e, boolean positive, java.util.function.BiConsumer<Core, S> per) {
        S out = readInto(e, positive, per);
        if (per != null) {
            per.accept(e, out);
        }
        return out;
    }

    private S readInto(Core e, boolean positive, java.util.function.BiConsumer<Core, S> per) {
        Core under = Conditions.negated(e);
        if (under != null) {
            return read(under, !positive, per);
        }
        if (e instanceof Core.Binary bin) {
            // Stated, a conjunction gives both sides; denied, it gives the choice between their
            // denials. And the same the other way round, which is the whole of what a denial does
            // to a connective.
            if (bin.op() == BinOp.AND) {
                return positive ? both(read(bin.left(), true, per), read(bin.right(), true, per))
                        : either(read(bin.left(), false, per), read(bin.right(), false, per));
            }
            if (bin.op() == BinOp.OR) {
                return positive ? either(read(bin.left(), true, per), read(bin.right(), true, per))
                        : both(read(bin.left(), false, per), read(bin.right(), false, per));
            }
        }
        return leaf(e, positive);
    }
}
