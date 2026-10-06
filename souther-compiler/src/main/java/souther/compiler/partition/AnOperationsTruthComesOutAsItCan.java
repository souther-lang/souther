package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.flow.ComparisonWays;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.UnaryOperator;

/**
 * The ways a value comes out in a tree where the language's operations stand, with a truth one of
 * them answers coming out each way it can.
 *
 * <p>The tree's own reading answers for comparisons and for a truth at a position, and an
 * operation's answer is a value it cannot witness. Left there, a condition written
 * {@code a > 0 || List.isEmpty(xs)} was one way through and not three: the second part arrived as a
 * value nothing named, and the rules a body draws by it were the fork's two arms with nothing in
 * between.
 *
 * <p>Asked one way at a time, as {@link ComparisonWays} asks: whether some value brings the truth
 * out {@code want}. That is a question about which answers the truth can give and not about whether
 * it varies, so it is answered with which ones those are ({@link Outcomes}).
 */
final class AnOperationsTruthComesOutAsItCan implements ComparisonWays {

    /**
     * Which answers a truth can give, as far as this reading can say.
     *
     * <p>Four and not two. A truth the same whatever the input gives one answer, and which one is a
     * second question this reading can answer for some values and not others: an emptiness check
     * over a list written out is answered by the list, and an operation this compiler does not
     * fold is not answered at all. Held as one word, a truth fixed at false would say it comes out
     * true as readily as a truth that varies does, and a way through it the other way round would
     * be a rule no row can take.
     */
    enum Outcomes {
        /** It may come out either way. */
        EITHER,
        /** It comes out true and never false. */
        ONLY_TRUE,
        /** It comes out false and never true. */
        ONLY_FALSE,
        /**
         * It comes out one way whatever the input, and which one this reading cannot say.
         *
         * <p>No way is stood behind, which is what the tree's own reading answers of a value it
         * cannot witness: the way through it is kept as one, and nothing is claimed of either.
         */
        ONE_WAY_UNSAID;

        boolean allows(boolean want) {
            return switch (this) {
                case EITHER -> true;
                case ONLY_TRUE -> want;
                case ONLY_FALSE -> !want;
                case ONE_WAY_UNSAID -> false;
            };
        }

        private Outcomes denied() {
            return switch (this) {
                case ONLY_TRUE -> ONLY_FALSE;
                case ONLY_FALSE -> ONLY_TRUE;
                case EITHER, ONE_WAY_UNSAID -> this;
            };
        }

        private static Outcomes only(boolean value) {
            return value ? ONLY_TRUE : ONLY_FALSE;
        }
    }

    private final InputReads reads;
    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;

    AnOperationsTruthComesOutAsItCan(InputReads reads, Symbols symbols,
                                     DeclarationNewtypes newtypes) {
        this.reads = reads;
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    @Override
    public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        if (ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy)) {
            return true;
        }
        return Core.withoutStanding(e) instanceof Core.PreservedCall applied
                && applied.type() == Type.Prim.BOOL
                && outcomesOf(applied, reads).allows(want);
    }

    @Override
    public ComparisonWays entering(ScopeStep step) {
        InputReads inside = reads.entering(step, symbols, newtypes);
        return inside == reads ? this
                : new AnOperationsTruthComesOutAsItCan(inside, symbols, newtypes);
    }

    /**
     * Which answers {@code truth} can give.
     *
     * <p>The answer it is fixed at where this reading can say it, read off what the source wrote:
     * a truth written out, a denial of one it can say, an emptiness check over a container written
     * out — which is how many elements were written — and what the checker folds. Otherwise either,
     * unless the walk partition reads a fork with found it the same whatever the input.
     */
    private Outcomes outcomesOf(Core truth, InputReads at) {
        // What the truth stands for, with the bindings it stands under: a denial the library
        // writes as a body binds what it denies, and that name is read where the binding is.
        Denotation stands = at.denotes(truth, symbols, newtypes);
        InputReads here = stands.at();
        UnaryOperator<Core> denotes = one -> here.denotes(one, symbols, newtypes).value();
        Core e = Core.withoutStanding(stands.value());
        if (e instanceof Core.Bool written) {
            return Outcomes.only(written.value());
        }
        Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, true);
        if (denied.isPresent()) {
            Outcomes under = outcomesOf(denied.get().part(), here);
            return denied.get().positive() ? under : under.denied();
        }
        Optional<Boolean> counted = emptinessWrittenOut(e, denotes);
        if (counted.isPresent()) {
            return Outcomes.only(counted.get());
        }
        Optional<Boolean> folded = BooleanMeaning.folded(e, symbols);
        if (folded.isPresent()) {
            return Outcomes.only(folded.get());
        }
        return WhatAForkTests.answersTheSameWhateverTheInput(e, denotes)
                ? Outcomes.ONE_WAY_UNSAID : Outcomes.EITHER;
    }

    /**
     * Whether a container written out is empty, where {@code e} is the library's emptiness check
     * of one — or empty where it is not.
     */
    private static Optional<Boolean> emptinessWrittenOut(Core e, UnaryOperator<Core> denotes) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall check)
                || check.args().size() != 1
                || DefaultBoundOperationFacts.get()
                        .meansTheSameAsASizeOfNought(check.declared().operation()) == null) {
            return Optional.empty();
        }
        return switch (Core.withoutStanding(denotes.apply(check.args().getFirst()))) {
            case Core.ListLit list -> Optional.of(list.elements().isEmpty());
            case Core.Str text -> Optional.of(text.value().isEmpty());
            case null, default -> Optional.empty();
        };
    }
}
