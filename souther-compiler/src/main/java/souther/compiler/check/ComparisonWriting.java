package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.BinOp;

/**
 * Writing a comparison down, which is the one way back from what a rule means to how one is
 * written.
 *
 * <p>Everything else here goes the other way. An operator is read for what it places once, where a
 * comparison is recognised ({@link ComparisonPlacement}), and every reader below that point holds
 * what was placed. A reading that composes a new comparison — one the source did not write, put
 * together out of what the rules proved — has to say it in the language's own operators, and this
 * is where that is said.
 *
 * <p><b>Beside {@link ComparisonClaim} rather than on it.</b> What a comparison placed is the
 * partition a rule drew, and nothing about a partition is an operator; a claim that could hand one
 * back is a claim every reader can ask for an operator, and asking an operator what it means is
 * exactly what the readings below a recognition stopped doing. So the way back takes a relation —
 * what the numeric reasoning states, which is what a composed comparison is composed out of — and
 * lives in one place a caller has to name.
 */
final class ComparisonWriting {

    private ComparisonWriting() {}

    /**
     * The operator a comparison stating {@code rel} of its two sides is written with.
     *
     * <p>Exact, and it has to be: what is written here is read back as a comparison by everything
     * downstream, so an operator that states something else is a rule the source never wrote
     * arriving with the source's own position on it.
     */
    static BinOp operatorStating(Rel rel) {
        return switch (rel) {
            case GE -> BinOp.GE;
            case GT -> BinOp.GT;
            case LE -> BinOp.LE;
            case LT -> BinOp.LT;
            case EQ -> BinOp.EQ;
            case NE -> BinOp.NE;
        };
    }
}
