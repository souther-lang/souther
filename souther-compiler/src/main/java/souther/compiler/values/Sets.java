package souther.compiler.values;

import souther.compiler.regex.Language;
import souther.compiler.regex.Meter;
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
    /** What each position is allowed and has spent, entered when it is first built at. */
    private final Map<A, Meter> meters = new LinkedHashMap<>();
    /** The positions whose exact answer this stopped building, in the order they were found. */
    private final Set<A> spent = new LinkedHashSet<>();
    /**
     * What a set belonging to no position is allowed, and whether it was given up on.
     *
     * <p>A reading holds one of those: what it guarantees at every position it holds no guarantee
     * for. It is not any position's, so it cannot be charged to one — a set standing for all of
     * them, put on the first position that happened to be met, would take the allowance of a
     * position whose own rules had not been read yet.
     */
    private final Meter elsewhere;
    private boolean spentElsewhere;

    private Sets(PatternPlan.Budget budget) {
        this.budget = budget;
        this.elsewhere = budget.meter();
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
     * <p>Not how a reader learns of it. What each of them left is in the reading already — a
     * {@link Composed} carried the widening and the shortfall to whoever asked, together, so
     * neither can arrive without the other — and this is the same fact gathered, for holding the
     * allowance to what it is supposed to do.
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
        // The meters themselves and not copies of them: what a position has spent is what it has
        // spent, and two allowances for one answer would be the renaming buying it twice.
        meters.forEach((atom, meter) -> out.meters.put(naming.apply(atom), meter));
        spent.forEach(atom -> out.spent.add(naming.apply(atom)));
        out.spentElsewhere = spentElsewhere;
        return out;
    }

    /**
     * The strings {@code syntax} accepts, as the values one position may hold.
     *
     * <p>Where a pattern becomes a set, and the only place. A pattern read but not built is a
     * position this says nothing about, which is what every other rule it cannot use leaves.
     */
    public Composed matching(A atom, PatternSyntax syntax) {
        return admitted(atom, PatternPlan.of(syntax));
    }

    /** What {@code plan} comes to, out of what the position is allowed. */
    private Composed admitted(A atom, PatternPlan plan) {
        return built(atom, meter -> plan.compile(meter));
    }

    /**
     * The strings {@code syntax} does not accept, as the values one position may hold.
     *
     * <p>What a pattern denied leaves, which is a set as surely as what it stated leaves. Built
     * here rather than by complementing a language afterwards, because the complement is the
     * expensive operation — a machine has to be made deterministic before a walk over it can be
     * turned around — and doing it out there would be doing it where nothing is counting.
     */
    public Composed notMatching(A atom, PatternSyntax syntax) {
        return admitted(atom, EVERY_STRING.less(PatternPlan.of(syntax)));
    }

    /**
     * Every string there is, as a plan to take one away from.
     *
     * <p>Any symbol, any number of times. Written as the symbols and not as a dot, which leaves out
     * the five line terminators — a denial that admitted every string but those would refuse values
     * a model may hold.
     */
    private static final PatternPlan EVERY_STRING = PatternPlan.of(
            new PatternSyntax.Repeated(new PatternSyntax.Symbols(
                    souther.compiler.regex.CodePoints.EVERYTHING),
                    0, PatternSyntax.Repeated.NO_CEILING));

    /**
     * What two sets neither of which is a language come to, which costs nothing either way.
     *
     * <p>Here so that the arithmetic over values a rule wrote out is written once. A plan puts two
     * of them together while it is being normalised, where there is nothing to build and no meter
     * to spend; the table below reaches the same cases when a language is on one side. Written
     * twice, the day one of them learned something the other did not would be a day two readings of
     * one model disagreed.
     */
    static ValueSet metPlainly(ValueSet one, ValueSet other) {
        return plainly(one, other, true);
    }

    /** The same for a choice. */
    static ValueSet joinedPlainly(ValueSet one, ValueSet other) {
        return plainly(one, other, false);
    }

    private static ValueSet plainly(ValueSet one, ValueSet other, boolean met) {
        if (one instanceof ValueSet.Matching || other instanceof ValueSet.Matching) {
            throw new IllegalArgumentException(
                    "a language is put together where there is an allowance for it");
        }
        // Nothing here builds, so the meter is never asked and what it allows does not matter.
        ValueSet made = met ? metUnder(one, other, PatternPlan.Budget.OF_ADMITTED_VALUES.meter())
                : joinedUnder(one, other, PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        return made;
    }

    /**
     * The values both admit, or null where making them ran past what {@code meter} allows.
     *
     * <p>The one table there is, and the one place the shapes are told apart. What each pair costs
     * is what it builds: a finite set is arithmetic over values in hand however it is paired, and
     * two languages are a machine.
     */
    public static ValueSet metUnder(ValueSet one, ValueSet other, Meter meter) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there -> new ValueSet.Finite(
                        kept(here.values(), there.values()::contains));
                case ValueSet.Cofinite there -> new ValueSet.Finite(
                        kept(here.values(), each -> !there.excluded().contains(each)));
                // Which of finitely many the language holds, asked of each. Exact and free: what
                // comes out is a subset of what was already written down, so no machine is made.
                case ValueSet.Matching there -> new ValueSet.Finite(
                        kept(here.values(), there::has));
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> metUnder(other, one, meter);
                case ValueSet.Cofinite there ->
                        new ValueSet.Cofinite(both(here.excluded(), there.excluded()));
                case ValueSet.Matching _ -> metUnder(other, one, meter);
            };
            case ValueSet.Matching here -> switch (other) {
                case ValueSet.Finite there -> new ValueSet.Finite(
                        kept(there.values(), here::has));
                // The language less what is excluded, which is a language: a value written out is
                // a string the machine can be told to refuse, and the rest is untouched.
                case ValueSet.Cofinite there ->
                        matching(here.language().without(textsIn(there.excluded()), meter));
                case ValueSet.Matching there ->
                        matching(here.language().and(there.language(), meter));
            };
        };
    }

    /** The values either admits, on the same terms. */
    public static ValueSet joinedUnder(ValueSet one, ValueSet other, Meter meter) {
        return switch (one) {
            case ValueSet.Finite here -> switch (other) {
                case ValueSet.Finite there ->
                        new ValueSet.Finite(both(here.values(), there.values()));
                // Everything the other admits, less what it excludes and this does not have: a
                // value it excludes is admitted here where this names it, so it is no longer
                // excluded from the two of them together.
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.values().contains(each)));
                case ValueSet.Matching _ -> joinedUnder(other, one, meter);
            };
            case ValueSet.Cofinite here -> switch (other) {
                case ValueSet.Finite _ -> joinedUnder(other, one, meter);
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(here.excluded(), there.excluded()::contains));
                case ValueSet.Matching _ -> joinedUnder(other, one, meter);
            };
            case ValueSet.Matching here -> switch (other) {
                // The language and the values written beside it, which is a language: what a set of
                // words costs to add is the words.
                case ValueSet.Finite there ->
                        matching(here.language().with(textsIn(there.values()), meter));
                // Everything except what is excluded and the language does not hold. A value
                // excluded there is admitted here where the language holds it, so it is excluded
                // from the two of them together only where neither has it — which is asked of each
                // of finitely many and builds nothing.
                case ValueSet.Cofinite there -> new ValueSet.Cofinite(
                        kept(there.excluded(), each -> !here.has(each)));
                case ValueSet.Matching there ->
                        matching(here.language().or(there.language(), meter));
            };
        };
    }

    /** The set a language came to, or null where it was not built. */
    private static ValueSet matching(Language made) {
        return made == null ? null : ValueSet.matching(made);
    }

    /** The values both admit — what two rules stated together leave a position. */
    public Composed meet(A atom, ValueSet one, ValueSet other) {
        return put(atom, one, other, true);
    }

    /** The values either admits — what a rule stated as one of two alternatives leaves. */
    public Composed join(A atom, ValueSet one, ValueSet other) {
        return put(atom, one, other, false);
    }

    /**
     * Either of them, out of what the position is allowed.
     *
     * <p>The shapes are told apart in one place ({@link #metUnder}), and what is here is the
     * allowance: which position pays, whether it has already been given up on, and what a refusal
     * leaves. Written twice, a pair that built something on one side and not on the other would be
     * two answers to what a position admits.
     */
    private Composed put(A atom, ValueSet one, ValueSet other, boolean met) {
        if (isSpent(atom) && (one instanceof ValueSet.Matching
                || other instanceof ValueSet.Matching)) {
            return gaveUp(atom);
        }
        Meter meter = meter(atom);
        ValueSet made = met ? metUnder(one, other, meter) : joinedUnder(one, other, meter);
        return made == null ? gaveUp(atom) : new Composed(made, false);
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
     * One machine, made out of what the position is allowed and counted as it is made.
     *
     * <p>What it will cost is not worked out here and is not worked out anywhere. A meet is at most
     * the two sizes multiplied and is usually far less, so a caller deciding on that number refuses
     * answers it could afford and charges for states nobody built. The meter says no at the state
     * that would have been one too many ({@link Meter}), and what comes back here is either a
     * language or nothing.
     */
    private Composed built(A atom, java.util.function.Function<Meter, Language> make) {
        if (isSpent(atom)) {
            return gaveUp(atom);
        }
        Language made = make.apply(meter(atom));
        return made == null ? gaveUp(atom)
                : new Composed(ValueSet.matching(made), false);
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
    private Meter meter(A atom) {
        return atom == null ? elsewhere : meters.computeIfAbsent(atom, _ -> budget.meter());
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
