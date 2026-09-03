package souther.compiler.values;

import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternPlan;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What each position of one answer is allowed to build, and everything that builds under it.
 *
 * <p>Held per position, because a position is what an answer is about: every rule reaching one pays
 * into the machine it finally admits, whether the rules are two halves of a clause, two clauses of
 * one declaration, or two declarations met by whoever needed both. One allowance for the whole
 * reading instead would let a complicated rule at one position spend what a plain one at another was
 * going to need, and which of them went unanswered would turn on the order they were written in.
 *
 * <p><b>One answer, one allowance.</b> Turning a rule into the set it names and putting a position's
 * sets together are the same spending, and so is putting two readings' answers together afterwards —
 * what comes out of that is a third set nobody has paid for. An answer given a fresh allowance for
 * each of those may spend its whole budget several times over, and the bound would be on a phase
 * rather than on the answer.
 *
 * <p><b>And nothing composes outside it.</b> Everything that may build is asked for through
 * {@link AdmittedPlan} and worked out by a {@link Realizer}, which is what makes the order the work
 * is done in a function of what is being asked rather than of who asked first. Two sets put together
 * by whoever held them would be a fold in arrival order again, one layer further out.
 *
 * @param <A> what a position is called
 */
public final class Allowance<A> {

    private final PatternPlan.Budget budget;
    private final Map<A, Meter> meters = new LinkedHashMap<>();
    private final Map<A, Realizer> realizers = new LinkedHashMap<>();
    /** The positions whose exact answer this stopped building, in the order they were found. */
    private final Set<A> spent = new LinkedHashSet<>();
    private Realizer nowhere;
    private boolean spentElsewhere;

    private Allowance(PatternPlan.Budget budget) {
        this.budget = budget;
    }

    /** A fresh allowance for every position of one answer. */
    public static <A> Allowance<A> of(PatternPlan.Budget budget) {
        if (budget == null) {
            throw new IllegalArgumentException("an allowance allows something");
        }
        return new Allowance<>(budget);
    }

    /** The same, at what one answer of a declaration is allowed. */
    public static <A> Allowance<A> ofAdmittedValues() {
        return of(PatternPlan.Budget.OF_ADMITTED_VALUES);
    }

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

    /** The values both admit — what two rules stated together leave a position. */
    public Composed meet(A atom, ValueSet one, ValueSet other) {
        return put(atom, AdmittedPlan.meeting(both(one, other)));
    }

    /** The values either admits — what a rule stated as one of two alternatives leaves. */
    public Composed join(A atom, ValueSet one, ValueSet other) {
        return put(atom, AdmittedPlan.joining(both(one, other)));
    }

    /**
     * The values any of them admits, said as one plan over all of them.
     *
     * <p>For a caller holding several at once, which is what a position holds across the
     * alternatives of a reading. Handed over together they are one plan however they were held, so
     * what they come to is worked out in the order the plan settles and costs one number. Folded
     * two at a time by the caller, the order would be the order it happened to hold them in — and a
     * set is a set however it was filled, so the same alternatives would cost two different things.
     */
    public Composed joining(A atom, List<ValueSet> these) {
        return put(atom, AdmittedPlan.joining(these.stream().map(AdmittedPlan::of).toList()));
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

    private static List<AdmittedPlan> both(ValueSet one, ValueSet other) {
        return List.of(AdmittedPlan.of(one), AdmittedPlan.of(other));
    }

    /**
     * What a plan comes to at {@code atom}, out of what that position is allowed.
     *
     * <p>Said as a plan and then worked out, rather than built as the two sets are handed over.
     * Which is what puts the order the work is done in with the thing being asked for: two sets are
     * one plan however they arrived, so what they cost is one number, and a plan already worked out
     * is not worked out again.
     *
     * <p>A position given up on stays given up on. Once the exact answer is not being built,
     * everything after it is about a set this compiler made wider, and buying a machine to narrow
     * something already widened is spending on an answer nobody can use.
     */
    private Composed put(A atom, AdmittedPlan plan) {
        if (isSpent(atom)) {
            return gaveUp(atom);
        }
        Realization made = at(atom).of(plan);
        return made.isExact() ? new Composed(made.upperBound(), false) : gaveUp(atom);
    }

    /**
     * What works a position's plans out, and what it has left to do it with.
     *
     * <p>One per position and kept, so a plan worked out twice is worked out once — which is what
     * lets a caller ask early without the position paying twice, and what makes when it was asked
     * no part of what it cost.
     */
    public Realizer realizer(A atom) {
        return realizers.computeIfAbsent(atom, _ -> new Realizer(meter(atom)));
    }

    /**
     * The same for a set belonging to no position.
     *
     * <p>A reading holds one of those: what it guarantees at every position it holds no guarantee
     * for. It is not any position's, so it cannot be charged to one — put on the first position
     * that happened to be asked, it would take the allowance of a position whose own rules had not
     * been read yet.
     */
    public Realizer elsewhere() {
        if (nowhere == null) {
            nowhere = new Realizer(budget.meter());
        }
        return nowhere;
    }

    private Realizer at(A atom) {
        return atom == null ? elsewhere() : realizer(atom);
    }

    /**
     * What {@code plan} was already worked out to admit at {@code atom}, or null where nothing
     * worked it out.
     *
     * <p>The one way to ask this allowance a question without spending it, and it is for the
     * accounts. What a rule of the model did to a position is read off the answer that was built
     * for the position; asked by building, an account would be paying out of the budget the answer
     * is bounded by, and a limit reached while attributing a reason would show up as the compiler
     * being less able to answer about the model.
     *
     * <p>Null is "nothing established this" and never "this admits everything". The two read alike
     * to a careless caller and mean opposite things: one is a fact about the values, and the other
     * is an absence of evidence that a caller answers by declining to claim.
     */
    public ValueSet known(A atom, AdmittedPlan plan) {
        return at(atom).known(plan) instanceof Realization.Exact it ? it.set() : null;
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
     * How much {@code atom} has left, for a caller holding this allowance to what it spent.
     *
     * <p>Not how a reader learns anything about a model. What each position came to and whether it
     * is exact is in the reading; this is the number itself, for measuring that the same rules cost
     * the same.
     */
    public int left(A atom) {
        return meter(atom).left();
    }

    /**
     * The same allowance, filed under what {@code naming} calls each position.
     *
     * <p>One answer and not two. A reading renamed into another vocabulary is the same answer being
     * built under other names, so what a position has spent goes with it — given a fresh allowance,
     * a position would be allowed its machine once on each side of the renaming and the product of
     * the two would be bought by nobody. The meters and the worked-out answers themselves, and not
     * copies of them, for that reason.
     */
    public <B> Allowance<B> renamed(java.util.function.Function<A, B> naming) {
        Allowance<B> out = new Allowance<>(budget);
        meters.forEach((atom, meter) -> out.meters.put(naming.apply(atom), meter));
        realizers.forEach((atom, made) -> out.realizers.put(naming.apply(atom), made));
        spent.forEach(atom -> out.spent.add(naming.apply(atom)));
        out.nowhere = nowhere;
        out.spentElsewhere = spentElsewhere;
        return out;
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

    /** Whether the exact answer here was already given up on. */
    private boolean isSpent(A atom) {
        return atom == null ? spentElsewhere : spent.contains(atom);
    }

    private Meter meter(A atom) {
        return meters.computeIfAbsent(atom, _ -> budget.meter());
    }
}
