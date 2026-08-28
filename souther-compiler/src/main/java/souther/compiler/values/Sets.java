package souther.compiler.values;

import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternSyntax;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Where two sets of values are put together, and what this compiler can afford to build by doing it.
 *
 * <p>Two questions, and they are not the same one. {@link ValueSet} says which values a position
 * holds; this says whether the set that answering exactly would take is one that can be made. So the
 * first is a value and stays one — two equal sets are equal wherever they came from — and the
 * allowance lives out here, with the reading that is spending it.
 *
 * <p><b>Held per position and not per rule.</b> What is being built is the set of values one
 * position finally admits, and every rule about that position pays into the same machine: two
 * patterns stated in one clause meet, and so do two stated in different rules of one declaration.
 * Given one allowance for the whole reading instead, a complicated pattern at one position would
 * spend what a plain one at another was going to need, and which of the two went unanswered would
 * turn on the order they were written in.
 *
 * <p><b>Nothing narrows on the way out.</b> Where the allowance is gone, what comes back is
 * {@link ValueSet#ANY} — every value there is, which is what is known once the exact answer is not
 * being built — together with the fact that it is not the exact answer. The two arrive as one
 * {@link Composed}, so a caller cannot take the set and leave the shortfall: a widening whose reason
 * went missing is a reading that says a position admits everything and means that nobody looked.
 *
 * <p>Only what builds a machine is charged, and only that is refused. A meet of two finite sets is
 * arithmetic over values that were already written down, and it stays exact at a position whose
 * allowance has gone — there is nothing to buy.
 *
 * @param <A> what a position is called
 */
public final class Sets<A> {

    /**
     * A set, and whether it is the exact one.
     *
     * <p>One value because the two are one fact. {@code gaveUp} does not describe the set — every
     * set here is an upper bound of what the rules leave, and this one is wider than it had to be.
     *
     * @param set what the two sides come to, or every value where the exact answer was not built
     * @param gaveUp whether building the exact answer was given up on for want of allowance
     */
    public record Composed(ValueSet set, boolean gaveUp) {

        public Composed {
            if (set == null) {
                throw new IllegalArgumentException("a composition comes to some set");
            }
        }
    }

    /**
     * One of the two ways two sets are put together, as something to hand to a caller that does not
     * care which.
     *
     * <p>The position is part of it, because the allowance is per position. A composer handed
     * without one would be a composition nobody could charge.
     */
    @FunctionalInterface
    public interface Composing<A> {

        /** What the two come to at {@code atom}, and whether it is the exact answer. */
        Composed of(A atom, ValueSet one, ValueSet other);
    }

    private final PatternPlan.Budget budget;
    /** What each position has left, entered when it is first spent at. */
    private final Map<A, int[]> left = new LinkedHashMap<>();
    /** The positions whose exact answer this stopped building, in the order they were found. */
    private final Set<A> spent = new LinkedHashSet<>();
    /**
     * What a set belonging to no position has left, and whether it was spent.
     *
     * <p>A reading holds one of those: what it guarantees at every position it holds no guarantee
     * for. It is not any position's, so it cannot be charged to one — a set standing for all of
     * them, put on the first position that happened to be met, would take the allowance of a
     * position whose own rules had not been read yet.
     */
    private final int[] elsewhere;
    private boolean spentElsewhere;

    private Sets(PatternPlan.Budget budget) {
        this.budget = budget;
        this.elsewhere = new int[] {budget.mostBuilt()};
    }

    /** A fresh allowance for every position of one reading. */
    public static <A> Sets<A> of(PatternPlan.Budget budget) {
        if (budget == null) {
            throw new IllegalArgumentException("a composer spends some allowance");
        }
        return new Sets<>(budget);
    }

    /** The same, at what one answer of a declaration is allowed. */
    public static <A> Sets<A> ofAdmittedValues() {
        return of(PatternPlan.Budget.OF_ADMITTED_VALUES);
    }

    /**
     * The positions whose exact answer was given up on, in the order they were found.
     *
     * <p>Read by whoever is answering for the reading as a whole. What each of them left is already
     * in the reading — a {@link Composed} said so where it happened — and this is the same fact
     * gathered, for a caller that has to say whether the measurement finished.
     */
    public Set<A> spent() {
        return Set.copyOf(spent);
    }

    /**
     * The same allowances, filed under what {@code naming} calls each position.
     *
     * <p>One derivation and not two. A reading renamed into another vocabulary is the same answer
     * being built under other names, so what a position has already spent goes with it — given a
     * fresh composer instead, a position would be allowed its machine once on each side of the
     * renaming and the product of the two would be bought by nobody.
     */
    public <B> Sets<B> renamed(java.util.function.Function<A, B> naming) {
        Sets<B> out = new Sets<>(budget);
        left.forEach((atom, purse) -> out.left.put(naming.apply(atom), purse));
        spent.forEach(atom -> out.spent.add(naming.apply(atom)));
        out.elsewhere[0] = elsewhere[0];
        out.spentElsewhere = spentElsewhere;
        return out;
    }

    /** Whether anything at all was given up on, the set belonging to no position included. */
    public boolean spentAnything() {
        return spentElsewhere || !spent.isEmpty();
    }

    /**
     * The strings {@code syntax} accepts, as the values one position may hold.
     *
     * <p>Where a pattern becomes a set, and the only place. A pattern read but not built is a
     * position this says nothing about, which is what every other rule it cannot use leaves.
     */
    public Composed matching(A atom, PatternSyntax syntax) {
        if (isSpent(atom)) {
            return gaveUp(atom);
        }
        int[] purse = purse(atom);
        Language made = PatternPlan.of(syntax).compile(
                new PatternPlan.Budget(Math.min(budget.mostStates(), purse[0]), purse[0]));
        if (made == null) {
            return gaveUp(atom);
        }
        purse[0] -= made.size();
        return new Composed(ValueSet.matching(made), false);
    }

    /** The values both admit — what two rules stated together leave a position. */
    public Composed meet(A atom, ValueSet one, ValueSet other) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there -> exact(new ValueSet.Finite(
                        kept(here.values(), there.values()::contains)));
                case ValueSet.Cofinite there -> exact(new ValueSet.Finite(
                        kept(here.values(), each -> !there.excluded().contains(each))));
                // Which of finitely many the language holds, asked of each. Exact and free: what
                // comes out is a subset of what was already written down, so no machine is made.
                case ValueSet.Matching there -> exact(new ValueSet.Finite(
                        kept(here.values(), there::has)));
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> meet(atom, other, one);
                case ValueSet.Cofinite there ->
                        exact(new ValueSet.Cofinite(both(here.excluded(), there.excluded())));
                case ValueSet.Matching _ -> meet(atom, other, one);
            };
            case ValueSet.Matching here -> switch (other) {
                case ValueSet.Finite there -> exact(new ValueSet.Finite(
                        kept(there.values(), here::has)));
                // The language less what is excluded, which is a language: a value written out is
                // a string the machine can be told to refuse, and the rest is untouched.
                case ValueSet.Cofinite there -> {
                    Set<String> words = textsIn(there.excluded());
                    yield built(atom, here.language().size() * (letters(words) + 2),
                            most -> here.language().without(words, most));
                }
                case ValueSet.Matching there ->
                        built(atom, (long) here.language().size() * there.language().size(),
                                most -> here.language().and(there.language(), most));
            };
        };
    }

    /** The values either admits — what a rule stated as one of two alternatives leaves. */
    public Composed join(A atom, ValueSet one, ValueSet other) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there ->
                        exact(new ValueSet.Finite(both(here.values(), there.values())));
                // Everything the other admits, less what it excludes and this does not have: a
                // value it excludes is admitted here where this names it, so it is no longer
                // excluded from the two of them together.
                case ValueSet.Cofinite there -> exact(new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.values().contains(each))));
                case ValueSet.Matching _ -> join(atom, other, one);
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> join(atom, other, one);
                case ValueSet.Cofinite there -> exact(new ValueSet.Cofinite(
                        kept(here.excluded(), there.excluded()::contains)));
                case ValueSet.Matching _ -> join(atom, other, one);
            };
            case ValueSet.Matching here -> switch (other) {
                // The language and the values written beside it, which is a language: what a set of
                // words costs to add is the words.
                case ValueSet.Finite there -> {
                    Set<String> words = textsIn(there.values());
                    yield built(atom, here.language().size() + letters(words) + 2L,
                            most -> here.language().with(words, most));
                }
                // Everything except what is excluded and the language does not hold. A value
                // excluded there is admitted here where the language holds it, so it is excluded
                // from the two of them together only where neither has it — which is asked of each
                // of finitely many and builds nothing.
                case ValueSet.Cofinite there -> exact(new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.has(each))));
                case ValueSet.Matching there -> built(atom,
                        here.language().size() + there.language().size() + 2L,
                        most -> here.language().or(there.language(), most));
            };
        };
    }

    /**
     * The same two, where what comes out is a promise rather than a bound.
     *
     * <p>Giving up leaves nothing and not everything, which is the other direction. What
     * {@link #meet} and {@link #join} answer is which values a position may hold, so an answer this
     * did not build widens to every value and stays true. A promise says which values it certainly
     * may hold, and every value is the strongest thing that can be said rather than the weakest —
     * so an unbuilt one promises nothing, and a reader is short of a guarantee instead of holding
     * one nobody proved.
     */
    public Composed meetPromised(A atom, ValueSet one, ValueSet other) {
        return promised(meet(atom, one, other));
    }

    /** The same for a choice, on the same terms. */
    public Composed joinPromised(A atom, ValueSet one, ValueSet other) {
        return promised(join(atom, one, other));
    }

    private static Composed promised(Composed made) {
        return made.gaveUp() ? new Composed(ValueSet.NONE, true) : made;
    }

    /**
     * One machine, where what it will cost is within what the position has left.
     *
     * <p>Asked before it is made and not after. A meet of two languages is the product of their
     * states, and a caller that built it to find out how big it was would have paid the whole price
     * of the answer it was deciding whether to afford.
     */
    private Composed built(A atom, long cost, java.util.function.IntFunction<Language> make) {
        if (isSpent(atom)) {
            return gaveUp(atom);
        }
        int[] purse = purse(atom);
        if (cost > purse[0] || cost > budget.mostStates()) {
            return gaveUp(atom);
        }
        // What it may spend and not what it will: the machine put together costs what was counted
        // above, and making it canonical is the rest of the price. Refused there too, since a
        // language handed out short of canonical is one whose next question does the work.
        Language made = make.apply(Math.min(budget.mostStates(), purse[0]));
        if (made == null) {
            return gaveUp(atom);
        }
        purse[0] -= made.size();
        return new Composed(ValueSet.matching(made), false);
    }

    private Composed exact(ValueSet set) {
        return new Composed(set, false);
    }

    /** Every value there is, and the fact that this is not what the rules leave. */
    private Composed gaveUp(A atom) {
        if (atom == null) {
            spentElsewhere = true;
        } else {
            spent.add(atom);
        }
        return new Composed(ValueSet.ANY, true);
    }

    /** What {@code atom} has left to spend, the reading's own allowance where it names no
     *  position. */
    private int[] purse(A atom) {
        return atom == null ? elsewhere
                : left.computeIfAbsent(atom, _ -> new int[] {budget.mostBuilt()});
    }

    /** Whether the exact answer here was already given up on. */
    private boolean isSpent(A atom) {
        return atom == null ? spentElsewhere : spent.contains(atom);
    }

    /** The strings among {@code values}, which are the only ones a language has a word for. */
    private static Set<String> textsIn(Set<Value> values) {
        Set<String> out = new LinkedHashSet<>();
        values.forEach(each -> {
            if (each instanceof Value.Text text) {
                out.add(text.value());
            }
        });
        return out;
    }

    /** What a set of words costs to make a machine of, which is their letters. */
    private static long letters(Set<String> words) {
        long out = 0;
        for (String each : words) {
            out += each.codePointCount(0, each.length());
        }
        return out;
    }

    private static Set<Value> kept(Set<Value> these, java.util.function.Predicate<Value> keep) {
        Set<Value> out = new LinkedHashSet<>();
        these.forEach(each -> {
            if (keep.test(each)) {
                out.add(each);
            }
        });
        return out;
    }

    private static Set<Value> both(Set<Value> these, Set<Value> those) {
        Set<Value> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }
}
