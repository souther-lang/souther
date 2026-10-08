package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;

import java.util.Optional;
import java.util.function.Predicate;

/**
 * A value the body asks the truth of, in the words a comparison is read in — for a reader outside
 * this package that reads conditions that way.
 *
 * <p>The checker's reading and not a second one. Which spellings deny what is under them is
 * {@link ClauseExpr}'s answer, and which operations mean a size compared against nought is
 * {@link Conditions#asSizeComparison}'s; a reader that worked either out for itself would be a
 * second account of what a condition says, free to disagree with the one a guard is settled by.
 *
 * <p>Two questions and not one, because what is under a denial may be a name. Where a name stands
 * for a value is the asker's reading of the body, which this has none of, so the denials are taken
 * off here and the asker follows what is left before asking what it means.
 */
public final class BooleanMeaning {

    private BooleanMeaning() {
    }

    /**
     * What a denial stands over, and whether the whole states it or denies it.
     *
     * @param part     what is under every denial, with none of them left on it
     * @param positive whether the whole coming out the way asked is {@code part} holding
     */
    public record UnderADenial(Core part, boolean positive) {}

    /**
     * What {@code truth}, asserted where {@code positive}, says of the value under its denials — or
     * empty where nothing denies it, or where it is a connective rather than one value.
     *
     * <p>A denial of what a binding answers is a denial of that binding: {@code Bool.not} handed a
     * helper's body denies the body, names and all. So what comes back there is the binding, and
     * the asker reads it in the names it binds.
     */
    public static Optional<UnderADenial> underADenial(Core truth, boolean positive) {
        return switch (ClauseExpr.of(truth, positive)) {
            case ClauseExpr.Leaf leaf when leaf.spelled().size() > 1 ->
                    Optional.of(new UnderADenial(leaf.of(), leaf.positive()));
            case ClauseExpr.Scoped scoped when scoped.spelled().size() > 1 ->
                    Optional.of(new UnderADenial(scoped.spelled().getLast(), scoped.positive()));
            default -> Optional.empty();
        };
    }

    /**
     * The truth {@code e} comes to at compile time, or empty where it is not one this compiler
     * folds.
     *
     * <p>The checker's folding ({@link CoreConstantEval}) and not a second one, under no binding
     * the reading was told of: a name is followed only where the tree still binds it.
     */
    public static Optional<Boolean> folded(Core e, Symbols symbols) {
        return CoreConstantEval.against(symbols, Denotations.none()).eval(e)
                .filter(Boolean.class::isInstance).map(Boolean.class::cast);
    }

    /**
     * A side of a comparison held against a truth the source settles, and which of its two values
     * the comparison coming out the way asked says it holds.
     *
     * @param side the side that is not the settled truth
     * @param held whether {@code side} holds
     */
    public record AgainstATruth(Core side, boolean held) {}

    /**
     * What {@code comparison}, coming out {@code holding}, says of a side of it held against a truth
     * the source settles, or empty where it holds none: {@code x == false} holding is {@code x} not
     * holding, and {@code x /= false} holding is {@code x} holding.
     *
     * <p>Which side is asked about is the asker's, by {@code subject}: a position of the input to
     * one reader, what a dependency answered to another. The relation and the folding are this
     * reading's, so the two read one spelling one way.
     *
     * @param subject whether a side is one the asker reads a truth of. The left side is asked first
     */
    public static Optional<AgainstATruth> againstATruth(StatedComparison comparison,
                                                         boolean holding, Symbols symbols,
                                                         Predicate<Core> subject) {
        Rel states = comparison.claim().statedRelation();
        Rel met = holding ? states : states.denied();
        if (met != Rel.EQ && met != Rel.NE) {
            return Optional.empty();
        }
        Core side = comparison.left();
        Core other = comparison.right();
        if (!subject.test(side)) {
            side = comparison.right();
            other = comparison.left();
            if (!subject.test(side)) {
                return Optional.empty();
            }
        }
        boolean equal = met == Rel.EQ;
        Core of = side;
        return folded(other, symbols).map(written -> new AgainstATruth(of, written == equal));
    }

    /**
     * The comparison {@code part} means, or empty where it means none.
     *
     * <p>A comparison is itself, and an emptiness check is its size against nought — a comparison
     * no source wrote, composed by this reading.
     *
     * <p>A statement and not a {@link Comparison}, because the second of those stands nowhere: the
     * binary an emptiness check is read as is this reading's, and handed out as a comparison it
     * would be a node a reader could ask where it is written. Where the statement came from is the
     * asker's, who holds the construct it asked about.
     */
    public static Optional<StatedComparison> asAComparison(Core part) {
        return Core.withoutStanding(Conditions.asSizeComparison(part)) instanceof Core.Binary binary
                ? Comparison.of(binary).map(Comparison::stated) : Optional.empty();
    }
}
