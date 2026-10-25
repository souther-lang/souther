package souther.compiler.numeric;

import souther.compiler.collect.AppendOnly;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What a path's rules leave the numbers in it, and what follows from them.
 *
 * <p>An atom is the numeric content of a variable, a field chain, or a newtype's wrapped value; what
 * names one is the caller's, and {@code Terms} in the checker is where the names come from today.
 * {@link #assume} takes in a {@code guard}/{@code if} guard or an input newtype's invariant, and
 * {@link #entails} / {@link #refutes} answer whether a construction's invariant is discharged or is
 * definitely violated on the current path — which is the invariant-discharge check, the caller this
 * was written for.
 *
 * <p><b>What is held is the rules, and everything else is worked out from them.</b> A rule arrives,
 * is read into the one form every writing of it comes to ({@link AffineConstraint}), and is kept.
 * Nothing is decided at the moment it arrives that depends on what had arrived before it. What the
 * rules leave is derived from all of them at once ({@link ClosedState}), once, when something asks.
 *
 * <p>That is not how this worked, and the difference is visible. A rule used to be sorted into a
 * bound, a difference, or a bucket of forms nothing read back, and the sorting looked at the
 * coefficients as they were typed — so {@code 2a - 2b <= 4} and {@code a - b <= 2} went to different
 * places and only one of them bounded anything. A disequality was turned into a bound or dropped
 * depending on what happened to be known at that moment, so {@code x /= 0} beside {@code x >= 0}
 * left {@code x} at nought or above according to which was written first. And a rule over several
 * positions was read only as something to subtract from a goal, never as something that narrows the
 * positions it names, so every range handed downstream was short of what the rules said.
 *
 * <p>Instances are immutable — each operation returns a fresh domain, threaded functionally like
 * {@code TotalityChecker}'s scope map. The arithmetic is exact throughout ({@link ExactRatio}),
 * which is what a form arrives holding: dividing is what deriving a bound does, and neither a
 * carrier's counts nor a model's decimals are closed under it. A bound becomes a
 * {@link BigDecimal} where it is handed to a reader that writes one ({@link #written}), and nowhere
 * else.
 */
public final class NumericDomain<A> {

    /**
     * How many digits a bound is written out to where it is not a decimal at all.
     *
     * <p>Almost never reached. A bound on a position whose values step lands on a whole number, and
     * a bound on one whose values fill is usually a decimal too; what is left is a bound at a value
     * like a third, which no decimal is. Rounded outward when it happens, so what is handed over
     * still admits everything the rules admit.
     */
    private static final int DIGITS_WHEN_IT_IS_NOT_A_DECIMAL = 34;

    private final StatedRules<A> stated;
    /** How the values at each position are spaced, told one rule at a time ({@link AppendOnly}). */
    private final AppendOnly<A, Granularity> kinds;
    /**
     * Where the order each atom's values are counted on stops, told where the atom is known
     * ({@link #heldInsideTheirOrders}). A fact about the position, as its spacing is, so it goes
     * with the names and with every domain met with this one: what a row holds is asked inside
     * these, and an answer that needed each asker to say them again was one an asker without them
     * gave of values no row holds.
     *
     * <p>Not a rule. Said as one, an order's end would be a bound the rules place, and every reader
     * of what the rules leave would read the type's end as a line the model draws.
     */
    private final AppendOnly<A, Bounds> orders;
    private final boolean readARuleNothingSatisfies;

    /**
     * The one order the positions of this domain are walked in, which the caller says because the
     * caller is the one that knows what a position of it is.
     *
     * <p>Carried and not part of what this domain is. What the rules leave is settled by the rules,
     * and two callers reading one set of rules under two orders read one domain — so this is the
     * same kind of thing as {@link #closed}: something a reading is worked out through rather than
     * something a reading is.
     */
    private final CanonicalOrder<A> order;

    /**
     * Where what the rules leave is worked out, and whether a closure another domain already worked
     * out stands for this one's.
     *
     * <p>Carried like {@link #order} and not part of what this domain is: it decides whether the
     * work is done again, never what it comes to. Lent to every domain made from this one, and to
     * whatever this one is met with — the receiver of a meeting is the reading the result belongs
     * to.
     */
    private final ClosedStates closedStates;

    /**
     * What the domain this one was made from had worked out by then, or the one before it — or
     * null where none had.
     *
     * <p>Carried like {@link #closedStates} and for the same kind of reason: its rules come first
     * among this one's, so the parts of them the rules said since do not reach are closures this one
     * need not work out again ({@link ClosedStates.Parted}). What this domain is, it never decides.
     */
    private final ClosedStates.Parted<A> closedBefore;

    /**
     * The rules the domain this one was made from had read by then, or the one before it — or null
     * where none had.
     *
     * <p>Carried like {@link #closedBefore}: what was said since is read onto them
     * ({@link #rules}), and what that comes to is what reading every rule said comes to.
     */
    private final RulesRead<A> readBefore;
    private RulesRead<A> read;
    private ClosedStates.Parted<A> closed;
    private Systems<A> systems;
    private Boolean noRow;

    private NumericDomain(StatedRules<A> stated, AppendOnly<A, Granularity> kinds,
                          AppendOnly<A, Bounds> orders,
                          boolean readARuleNothingSatisfies, CanonicalOrder<A> order,
                          ClosedStates closedStates, ClosedStates.Parted<A> closedBefore,
                          RulesRead<A> readBefore) {
        this.stated = stated;
        this.kinds = kinds;
        this.orders = orders;
        this.readARuleNothingSatisfies = readARuleNothingSatisfies;
        this.order = order;
        this.closedStates = closedStates;
        this.closedBefore = closedBefore;
        this.readBefore = readBefore;
    }

    /**
     * What a domain made from this one by saying more of its rules is lent: this one's closure where
     * it has been worked out, and otherwise what this one was lent.
     *
     * <p>Not worked out for the asking. A closure nobody asked this domain for is one a domain made
     * from it may never need either.
     */
    private ClosedStates.Parted<A> lent() {
        ClosedStates.Parted<A> had = closed;
        return had != null ? had : closedBefore;
    }

    /** The same for the rules read: this one's where they have been, and otherwise its loan. */
    private RulesRead<A> readLent() {
        RulesRead<A> had = read;
        return had != null ? had : readBefore;
    }

    /**
     * Everything, over positions {@code order} puts in one order.
     *
     * <p>Asked for the order here because working the rules out walks the positions of a form, and
     * what such a walk takes first has to be settled by the positions rather than by how the rules
     * were typed. What it is belongs to whatever a position of this domain is, which this is generic
     * over and the caller is not — see {@link CanonicalOrder}.
     *
     * <p>Each domain made from this works out what its rules leave for itself.
     */
    public static <A> NumericDomain<A> top(CanonicalOrder<A> order) {
        return top(order, ClosedStates.NONE);
    }

    /**
     * The same, with what the rules leave worked out through {@code closedStates} — so a domain made
     * from this one is lent the closure of any other made from it that held the same rules.
     */
    public static <A> NumericDomain<A> top(CanonicalOrder<A> order, ClosedStates closedStates) {
        return new NumericDomain<>(StatedRules.none(), AppendOnly.empty(), AppendOnly.empty(),
                false, order, closedStates, null, null);
    }

    /**
     * The rules said, each of them once, derived on the first question asked of them and kept.
     *
     * <p>Here rather than at each saying, for the reason {@link StatedRules} gives. Everything below
     * reads this and not what was said, so what any of them sees is a rule said twice said once.
     *
     * <p>Read onto what the domain this was made from had read, where its rules are the first of
     * these: what was said since is taken a rule at a time ({@link #readOnto}). Read from the start
     * at every step, a path stating a rule per step would read every rule it had stated at each one.
     */
    private List<AffineConstraint<A>> rules() {
        RulesRead<A> had = read;
        if (had == null) {
            had = new RulesRead<>(stated, readFrom(stated, readBefore));
            read = had;
        }
        return had.rules();
    }

    /**
     * The rules as every reader here reads them, for a test holding what is read onto an earlier
     * reading to what reading every rule said from the start comes to.
     */
    List<AffineConstraint<A>> rulesRead() {
        return rules();
    }

    /**
     * What a set of rules was read to, with the composition it was read from.
     *
     * <p>Held by the composition itself and not by one equal to it: a domain made from another by
     * saying more holds the other's composition at the left of its own, which is how the rules said
     * since are found without comparing anything.
     */
    private record RulesRead<A>(StatedRules<A> of, List<AffineConstraint<A>> rules) {}

    /**
     * {@code stated} read, onto {@code before} where {@code stated} is {@code before}'s rules
     * followed by others, and from the start otherwise.
     */
    private static <A> List<AffineConstraint<A>> readFrom(StatedRules<A> stated,
                                                          RulesRead<A> before) {
        if (before != null) {
            Deque<StatedRules<A>> since = new ArrayDeque<>();
            StatedRules<A> at = stated;
            while (at != before.of() && at instanceof StatedRules.Both<A> both) {
                since.push(both.right());
                at = both.left();
            }
            if (at == before.of()) {
                List<AffineConstraint<A>> out = before.rules();
                while (!since.isEmpty()) {
                    for (AffineConstraint<A> rule : since.pop().distinct()) {
                        out = readOnto(out, rule);
                    }
                }
                return out;
            }
        }
        return tightest(stated.distinct());
    }

    /**
     * {@code rules}, which are {@link #tightest} of the distinct rules said so far, with
     * {@code rule} said after them — what {@link #tightest} of the distinct rules with it comes to.
     *
     * <p>A rule other than a sum held below a bound is in the distinct rules exactly where it is in
     * these, since only such sums are left out, so asking these is asking whether it was said. A
     * sum held below a bound needs no asking: its form has one bound here, the tightest of those
     * said, and the tighter of that and one already among them is that one.
     */
    private static <A> List<AffineConstraint<A>> readOnto(List<AffineConstraint<A>> rules,
                                                          AffineConstraint<A> rule) {
        if (rule instanceof AffineConstraint.HalfSpace<A> half) {
            for (int at = 0; at < rules.size(); at++) {
                if (rules.get(at) instanceof AffineConstraint.HalfSpace<A> held
                        && held.form().equals(half.form())) {
                    ExactCut kept = ExactCut.tighterUpper(held.bound(), half.bound());
                    if (kept.equals(held.bound())) {
                        return rules;
                    }
                    List<AffineConstraint<A>> out = new ArrayList<>(rules);
                    out.set(at, new AffineConstraint.HalfSpace<>(half.form(), kept));
                    return List.copyOf(out);
                }
            }
        } else if (rules.contains(rule)) {
            return rules;
        }
        List<AffineConstraint<A>> out = new ArrayList<>(rules.size() + 1);
        out.addAll(rules);
        out.add(rule);
        return List.copyOf(out);
    }

    /**
     * {@code rules} with a sum held below several bounds held below the tightest of them, where the
     * first of them was said.
     *
     * <p>The others say nothing the tightest does not: a sum below it is below each of them. Kept,
     * they are rules every reader below reads again and every closure works again — a path that
     * multiplies one value by many numbers states a bound on it for each, each tighter than the
     * one before, and the closure asked at every step of that path would work over all of them.
     */
    private static <A> List<AffineConstraint<A>> tightest(List<AffineConstraint<A>> rules) {
        Map<CanonicalForm<A>, ExactCut> below = new LinkedHashMap<>();
        int halves = 0;
        for (AffineConstraint<A> rule : rules) {
            if (rule instanceof AffineConstraint.HalfSpace<A> half) {
                below.merge(half.form(), half.bound(), ExactCut::tighterUpper);
                halves++;
            }
        }
        if (below.size() == halves) {
            return rules;
        }
        List<AffineConstraint<A>> out = new ArrayList<>(rules.size());
        for (AffineConstraint<A> rule : rules) {
            if (!(rule instanceof AffineConstraint.HalfSpace<A> half)) {
                out.add(rule);
                continue;
            }
            ExactCut kept = below.remove(half.form());
            if (kept != null) {
                out.add(kept.equals(half.bound()) ? half
                        : new AffineConstraint.HalfSpace<>(half.form(), kept));
            }
        }
        return List.copyOf(out);
    }

    /**
     * Whether the rules leave nothing at all, in which case the path is not reached.
     *
     * <p>True is a proof and false is not — see {@link ClosedState#holdsNothing}. Everything that
     * narrows is implied by the rules, so an emptied box is one the rules emptied; the rounds can
     * stop early, so a box that has not emptied is not a box with a value in it.
     */
    public boolean isBottom() {
        return readARuleNothingSatisfies || closed().holdsNothing();
    }

    // --- assume: take in one more rule ------------------------------------------------------------

    /**
     * The domain with {@code f rel 0} taken in, where {@code f} was held.
     *
     * <p>A form this arithmetic could not hold is a rule it cannot write, which narrows nothing: the
     * sound answer with less, and the one {@link AffineConstraint.Read.NotWorkedOut} gives for a
     * rule whose lowest terms are not held.
     *
     * @param atomKinds see {@link #assume(LinearForm, Rel, Map)}
     */
    public NumericDomain<A> assume(ExactAnswer<LinearForm<A>> f, Rel rel,
                                   Map<A, Granularity> atomKinds) {
        return f instanceof ExactAnswer.Held<LinearForm<A>> held
                ? assume(held.value(), rel, atomKinds) : this;
    }

    /**
     * The domain with {@code f rel 0} taken in.
     *
     * @param atomKinds how the values of each atom of {@code f} are spaced. Required rather than
     *                  defaulted: an atom whose spacing is guessed is one a strict bound is either
     *                  wrongly sharpened on or silently left blunt, and neither shows up as a
     *                  failure anywhere near where the guess was made.
     */
    public NumericDomain<A> assume(LinearForm<A> f, Rel rel, Map<A, Granularity> atomKinds) {
        NumericDomain<A> knowing = knowing(f.coefs().keySet(), atomKinds);
        if (knowing.readARuleNothingSatisfies) {
            return knowing;
        }
        AffineConstraint.Read<A> read = AffineConstraint.of(
                f.coefs(), f.constant(), rel, knowing.kinds::get);
        return switch (read) {
            // Nothing satisfies it, so nothing satisfies it together with anything else.
            case AffineConstraint.Read.HoldsNever<A> _ ->
                    new NumericDomain<>(StatedRules.none(), knowing.kinds, knowing.orders, true,
                            knowing.order, closedStates, null, null);
            // Every value satisfies it, so there is nothing to keep.
            case AffineConstraint.Read.HoldsAlways<A> _ -> knowing;
            case AffineConstraint.Read.Stated<A> stated -> knowing.keeping(stated.constraint());
            // A rule this cannot write narrows nothing, which is the sound answer with less.
            case AffineConstraint.Read.NotWorkedOut<A> _ -> knowing;
        };
    }

    /**
     * The domain with one more rule kept.
     *
     * <p>Kept and not merged into anything. A rule said twice is the same rule and the same key, so
     * the second saying adds nothing — which is what makes the answer a function of which rules were
     * said rather than of how often each was. Which is settled where the rules are read
     * ({@link #rules}) and not here: looked for here, saying a rule would cost a walk of every rule
     * said before it, and a path stating many of them would pay that for each.
     */
    private NumericDomain<A> keeping(AffineConstraint<A> rule) {
        return new NumericDomain<>(stated.and(StatedRules.of(rule)), kinds, orders, false, order,
                closedStates, lent(), readLent());
    }

    /**
     * The domain refined by taking {@code atom} to lie between {@code bounds}.
     *
     * <p>Here rather than at each caller because what a range's ends are as assertions is this
     * domain's reading of them: an end the range does not reach is the strict comparison, and a
     * caller spelling that out is a second reader of an {@link Endpoint} that can spell it
     * differently. Two of them had.
     */
    public NumericDomain<A> assuming(A atom, Bounds bounds, Map<A, Granularity> atomKinds) {
        NumericDomain<A> out = this;
        if (bounds.min() != null) {
            out = out.assume(
                    LinearForm.atomMinusConstant(atom, Count.number(bounds.min().at()).exactly()),
                    bounds.min().inclusive() ? Rel.GE : Rel.GT, atomKinds);
        }
        if (bounds.max() != null) {
            out = out.assume(
                    LinearForm.atomMinusConstant(atom, Count.number(bounds.max().at()).exactly()),
                    bounds.max().inclusive() ? Rel.LE : Rel.LT, atomKinds);
        }
        return out;
    }

    /**
     * The domain with the spacing of each of {@code atoms} recorded.
     *
     * <p>One atom is one kind of number for as long as the domain lives. The same key arriving as
     * both is not a widening to absorb — the key is what says two readings are of one value, so two
     * spacings under one key means the naming and the typing disagree, and the answer to that is to
     * stop rather than to pick the safer of the two.
     */
    private NumericDomain<A> knowing(Set<A> atoms, Map<A, Granularity> atomKinds) {
        AppendOnly<A, Granularity> next = kinds;
        for (A atom : atoms) {
            Granularity given = atomKinds.get(atom);
            if (given == null) {
                throw new IllegalStateException("no granularity given for atom `" + atom + "`");
            }
            Granularity had = next.get(atom);
            if (had == given) {
                continue;
            }
            if (had != null) {
                throw new IllegalStateException("atom `" + atom + "` is " + had + " and " + given);
            }
            next = next.with(atom, given);
        }
        return next == kinds ? this
                : new NumericDomain<>(stated, next, orders, readARuleNothingSatisfies, order,
                        closedStates, lent(), readLent());
    }

    /**
     * The domain with where the order of each of {@code stops} is counted on stops recorded, by
     * atom.
     *
     * <p>Recorded and checked as a spacing is ({@link #knowing}): one atom is one kind of number
     * for as long as the domain lives, so two ends under one key is the naming and the typing
     * disagreeing, and the answer to that is to stop. What the rules leave does not move: the
     * rules are the same rules, and this says only which of their points a row can be.
     */
    public NumericDomain<A> heldInsideTheirOrders(Map<A, Bounds> stops) {
        AppendOnly<A, Bounds> next = orders;
        for (Map.Entry<A, Bounds> each : stops.entrySet()) {
            Bounds had = next.get(each.getKey());
            if (each.getValue().equals(had)) {
                continue;
            }
            if (had != null) {
                throw new IllegalStateException("atom `" + each.getKey() + "` stops at " + had
                        + " and " + each.getValue());
            }
            next = next.with(each.getKey(), each.getValue());
        }
        return next == orders ? this
                : new NumericDomain<>(stated, kinds, next, readARuleNothingSatisfies, order,
                        closedStates, lent(), readLent());
    }

    // --- renaming and joining ---------------------------------------------------------------------

    /**
     * The same rules over positions called something else.
     *
     * <p>For a reader that holds the rules of a value and is asked about them as rules of the thing
     * that holds it. What a rule says is a relation between positions, and a relation does not move
     * when the positions are called by another vocabulary's names — so this is a renaming and not a
     * second reading, and nothing about what the rules leave changes.
     *
     * <p>Every position a rule weighs has to have a name, and no two of them the same
     * ({@link Renaming}). A rule reaching a position the caller's vocabulary cannot spell
     * is a rule that cannot be carried across, and dropping it here would hand back a domain that
     * leaves more than these rules do — which is the one direction a reader downstream cannot see.
     * So the caller is the one that decides what such a position is called, and it may call it
     * something opaque; what it may not do is leave it unnamed and be given a wider answer.
     *
     * <p>The spacing goes with the names, since it is a fact about the position rather than about
     * the word for it. Every position a rule weighs is one this records a spacing for, so naming
     * them all is naming everything the rules are about — a rule reaching one this has no spacing
     * for is refused rather than carried across unnamed.
     */
    public <B> NumericDomain<B> over(java.util.function.Function<A, B> naming,
                                     CanonicalOrder<B> order) {
        // Settled once, over every position these rules speak of, which is what this holds and no
        // rule of it does. A rule asked whether a naming is one-to-one can only answer about its own
        // positions, so two independent rules would be carried across as two rules about one number
        // and a box holding something would come back holding nothing.
        Renaming<A, B> called = Renaming.of(kinds.keys(), naming);
        Map<B, Granularity> spacing = new LinkedHashMap<>();
        kinds.asMap().forEach((atom, spaced) -> spacing.put(called.of(atom), spaced));
        // And where each order stops, which is the same kind of fact. Of the positions the rules
        // speak of, which are the ones a row is asked about; an end told of a position no rule
        // names bounds nothing anybody asks.
        Map<B, Bounds> stops = new LinkedHashMap<>();
        orders.asMap().forEach((atom, stop) -> {
            if (kinds.contains(atom)) {
                stops.put(called.of(atom), stop);
            }
        });
        StatedRules<B> out = StatedRules.none();
        for (AffineConstraint<A> rule : rules()) {
            out = out.and(StatedRules.of(rule.over(called)));
        }
        // The order of the names arrived at, and not this one carried across. What puts two
        // positions in an order is a fact about what a position of that vocabulary is, and the
        // caller is the one that knows it — the same reason the order is asked for at the top.
        // Nothing is lent across either: rules under other names are another reader's rules, and
        // they join the closures of the reading they are met into.
        return new NumericDomain<>(out, AppendOnly.of(spacing), AppendOnly.of(stops),
                readARuleNothingSatisfies, order, ClosedStates.NONE, null, null);
    }

    /**
     * Everything both of these say.
     *
     * <p>Saying two sets of rules together, which is what a caller holding rules read of two values
     * at once has. Nothing is derived here — the rules are kept as they arrived and what they leave
     * is worked out when it is asked for, the same as when they arrive one at a time.
     *
     * <p>A rule in both is one rule, for the reason {@link #keeping} gives: a rule said twice is the
     * same rule, and an answer that depended on how often each was said would depend on how the
     * caller came by them.
     *
     * <p>Spacings are checked rather than merged, and so is where each order stops. Two readings
     * calling one position by one name and spacing it two ways is the naming and the typing
     * disagreeing, and picking the safer of the two would answer about a position neither reading
     * was about.
     *
     * <p>What the result leaves is worked out through this domain's {@link #closedStates} and not
     * through {@code other}'s. The receiver is the reading the result is part of, and that is
     * nothing about what the rules mean.
     */
    public NumericDomain<A> meet(NumericDomain<A> other) {
        if (other == null || (other.stated.isNothing() && other.kinds.isEmpty()
                && other.orders.isEmpty() && !other.readARuleNothingSatisfies)) {
            return this;
        }
        NumericDomain<A> held = heldInsideTheirOrders(other.orders.asMap());
        AppendOnly<A, Granularity> both = kinds;
        for (Map.Entry<A, Granularity> each : other.kinds.asMap().entrySet()) {
            Granularity had = both.get(each.getKey());
            if (had == null) {
                both = both.with(each.getKey(), each.getValue());
            } else if (had != each.getValue()) {
                throw new IllegalStateException("atom `" + each.getKey() + "` is " + had + " and "
                        + each.getValue());
            }
        }
        return new NumericDomain<>(stated.and(other.stated), both, held.orders,
                readARuleNothingSatisfies || other.readARuleNothingSatisfies, order, closedStates,
                // The rules said first are this one's, unless it has none and they are the other's.
                stated.isNothing() ? other.lent() : lent(),
                stated.isNothing() ? other.readLent() : readLent());
    }

    // --- what the rules leave, worked out once ----------------------------------------------------

    /**
     * The rules worked out, derived on the first question asked of them and kept.
     *
     * <p>Not while they are arriving. What a rule leaves depends on the others, and half of them have
     * not been said yet when it is said — a bound written down at that moment is a bound that depends
     * on the order, which is the thing this arrangement exists to be rid of.
     */
    private ClosedState<A> closed() {
        ClosedStates.Parted<A> had = closed;
        if (had == null) {
            had = closedStates.of(rules(), kinds::get, order, closedBefore);
            closed = had;
        }
        return had.state();
    }

    // --- entails / refutes --------------------------------------------------------------------------

    /** Whether the rules prove {@code f rel 0} — the construction's invariant is discharged. */
    public boolean entails(LinearForm<A> f, Rel rel) {
        return entails(f, rel, true);
    }

    /**
     * Whether the ranges, together with the relations the closure holds between them, prove
     * {@code f rel 0}.
     *
     * <p>Not the ranges on their own, and the difference matters. {@code a - b <= 2} beside two
     * positions the rules leave running 0 to 7 is not something the two ranges state — they hold
     * {@code a} at 7 beside {@code b} at 0 — and it is held exactly by the closed differences, which
     * this reads. So a rule of that shape comes back proven, and a reader taking this for "the
     * product of the ranges states it" is reading an answer about a stronger object than the one it
     * has.
     *
     * <p>For naming what could not be stated, and not for deciding whether a range is the whole of
     * what the rules leave a position. That decision is {@link #projectionCertification()}, which is
     * this asked of every rule at once <em>and</em> the hypotheses the step from here to a range
     * needs. Asked one rule at a time this answers about the rule; it does not answer about the
     * range.
     *
     * <p>A caller deciding whether a construction discharges its invariant wants {@link #entails}:
     * what is known there is everything the rules say, however they say it.
     */
    public boolean provenByTheBoxAndItsDifferences(LinearForm<A> f, Rel rel) {
        return entails(f, rel, false);
    }

    /**
     * Whether each position's box is the whole of what the rules leave it, and what settled that.
     *
     * <p>About the box this derives in exact arithmetic, and not about the number a caller is handed
     * at an end of it. A bound at a value no decimal writes is written out rounded outward, and
     * whether that happened is a question about the writing which the caller that does the writing
     * asks. What is certified here stops at the box.
     *
     * <p>A refusal is not "the box is wider". It is that nothing here showed it is the whole of it,
     * which is the only thing a caller may act on — see {@link ProjectionCertification}.
     */
    public ProjectionCertification projectionCertification() {
        if (isBottom()) {
            return new ProjectionCertification.NothingIsLeft();
        }
        if (!closed().everyBoundWasComposed()) {
            return new ProjectionCertification.ArithmeticLeftTheClosureIncomplete();
        }
        if (!everyRelatedPositionIsSpacedAlike()) {
            return new ProjectionCertification.PositionsSpacedDifferently();
        }
        for (AffineConstraint<A> rule : rules()) {
            if (!proven(rule, false)) {
                return new ProjectionCertification.NotEveryRuleIsProven();
            }
        }
        return new ProjectionCertification.Certified(
                new ProjectionCertificate.ByBoxAndClosedDifferences());
    }

    /**
     * Whether every position the rules relate to each other has its values spaced the same way.
     *
     * <p>Related and not merely present. The hypothesis belongs to the step from a system to one of
     * its ranges, and that step is taken through the relations — so what has to be of one kind is a
     * position and everything a chain of relations reaches from it. Two positions no rule mentions
     * together are two systems that happen to be written down beside each other, and a record with a
     * whole number in one field and a decimal in another is exactly that, which is most of them.
     *
     * <p>Related through the whole chain and not one rule at a time. The closure composes edges, so
     * a difference of two whole numbers beside a difference of one of them and a decimal leaves a
     * relation between a whole number and a decimal that nobody wrote — which is the same mixture,
     * one composition further on.
     */
    private boolean everyRelatedPositionIsSpacedAlike() {
        Map<A, A> reaches = related();
        return spacedAlike(reaches, List.copyOf(reaches.keySet()));
    }

    /** The groups the rules relate the positions in, each position pointing along the chain to
     *  its group ({@link #groupOf}). */
    private Map<A, A> related() {
        Map<A, A> reaches = new LinkedHashMap<>();
        for (AffineConstraint<A> rule : rules()) {
            A first = null;
            // Walked in the one order the positions decide. Which of a rule's positions the rest
            // are related to is what this writes down, and taken off the form as it is held that
            // would be the position the rule was typed first.
            for (A atom : rule.form().atomsIn(order)) {
                if (first == null) {
                    first = atom;
                    groupOf(reaches, atom);
                } else {
                    relate(reaches, first, atom);
                }
            }
        }
        return reaches;
    }

    /** Whether each of {@code atoms} has its values spaced as every other of its group has. */
    private boolean spacedAlike(Map<A, A> reaches, List<A> atoms) {
        Map<A, Granularity> ofGroup = new LinkedHashMap<>();
        for (A atom : atoms) {
            Granularity how = kinds.get(atom);
            if (how == null) {
                // Every atom of every rule is spaced, since a rule arrives through `assume` and that
                // refuses one whose spacing it was not given. Said rather than read as an absence:
                // put in the map as one, a null makes every later member of the group match it, and
                // a mixed group comes back alike — which promises an edge the theorem does not
                // reach, and does it silently.
                throw new IllegalStateException("no granularity given for atom `" + atom + "`");
            }
            Granularity had = ofGroup.putIfAbsent(groupOf(reaches, atom), how);
            if (had != null && had != how) {
                return false;
            }
        }
        return true;
    }

    /** The two positions put in one group, which is what one rule naming both of them says. */
    private static <A> void relate(Map<A, A> reaches, A one, A other) {
        A mine = groupOf(reaches, one);
        A theirs = groupOf(reaches, other);
        if (!mine.equals(theirs)) {
            reaches.put(mine, theirs);
        }
    }

    /** Which group a position is in, following the chain to its end. */
    private static <A> A groupOf(Map<A, A> reaches, A atom) {
        reaches.putIfAbsent(atom, atom);
        A at = atom;
        while (!reaches.get(at).equals(at)) {
            at = reaches.get(at);
        }
        return at;
    }

    /**
     * Whether the rules prove the comparison, read the one way a comparison is read.
     *
     * <p>Through {@link AffineConstraint#of} — the same reading a rule goes through on the way in.
     * What each of the six relations means was written here as well as there, so the two readings
     * could differ and did: the one on the way in divides a comparison through by what its weights
     * share and moves a bound onto a value the sum can take, and the one here did neither. A
     * question scaled away from the rule it needs was left with a residual nothing could prove, and
     * a difference asked with weights of two was not recognised as a difference at all.
     *
     * <p>So a question is not a second kind of thing. It is a comparison, which is what a rule is,
     * and it is read into the same three shapes.
     */
    private boolean entails(LinearForm<A> f, Rel rel, boolean withRules) {
        if (isBottom()) {
            return true;   // an infeasible path discharges anything
        }
        Map<A, ExactRatio> coefs = weighed(f);
        if (!coefs.keySet().stream().allMatch(kinds::contains)) {
            // A position this has never been told about is one nothing here bounds, so nothing here
            // proves about it either. Said before the reading, which would want its spacing.
            return false;
        }
        return switch (AffineConstraint.of(coefs, f.constant(), rel, kinds::get)) {
            case AffineConstraint.Read.HoldsAlways<A> _ -> true;
            case AffineConstraint.Read.HoldsNever<A> _ -> false;
            case AffineConstraint.Read.Stated<A> stated -> proven(stated.constraint(), withRules);
            // What could not be written is not proven, and not disproven either.
            case AffineConstraint.Read.NotWorkedOut<A> _ -> false;
        };
    }

    /**
     * Whether the rules prove what one constraint says.
     *
     * <p>Held below something is one thing to prove; held at something is the two the constraint
     * itself names; held away from something is either of two strict ones, since a sum away from a
     * value is under it or over it.
     */
    private boolean proven(AffineConstraint<A> asked, boolean withRules) {
        if (asked instanceof AffineConstraint.Disequality<A> hole) {
            return proves(below(hole.form(), hole.at()), true, withRules)
                    || proves(below(hole.form().negated(), hole.at().negated()), true, withRules);
        }
        for (AffineConstraint.HalfSpace<A> half : asked.halfSpaces()) {
            if (!proves(below(half.form(), half.bound().at()), !half.bound().inclusive(),
                    withRules)) {
                return false;
            }
        }
        return true;
    }

    /** {@code form - at}, which is what is bounded to decide whether {@code form <= at}. */
    private Goal<A> below(CanonicalForm<A> form, ExactRatio at) {
        return new Goal<>(form.coefs(), at.negated());
    }

    /**
     * Whether the rules prove {@code ¬(f rel 0)} — the invariant is <em>definitely</em> violated on
     * this path, which is a compile error rather than an undischarged obligation.
     *
     * <p>Which is proving the comparison that holds exactly where this one does not, and which one
     * that is belongs to the relation ({@link Rel#denied}).
     */
    public boolean refutes(LinearForm<A> f, Rel rel) {
        return !isBottom() && entails(f, rel.denied(), true);
    }

    /** A form's weights with the positions it does not actually weigh left out. A form composed by
     *  the arithmetic drops those as it goes; one built by naming its coefficients need not have. */
    private Map<A, ExactRatio> weighed(LinearForm<A> f) {
        Map<A, ExactRatio> coefs = new LinkedHashMap<>();
        f.coefs().forEach((atom, coef) -> {
            if (!coef.isZero()) {
                coefs.put(atom, coef);
            }
        });
        return coefs;
    }

    /** A goal as a weighted sum and a constant, which is what a comparison against nought is. */
    private record Goal<A>(Map<A, ExactRatio> coefs, ExactRatio constant) {

        Goal<A> negated() {
            Map<A, ExactRatio> out = new LinkedHashMap<>();
            coefs.forEach((atom, coef) -> out.put(atom, coef.negated()));
            return new Goal<>(out, constant.negated());
        }
    }

    /**
     * A canonical question and what the form it was asked about was multiplied by.
     *
     * <p>The divisor is nothing to a question about which side of nought a form falls — scaling by a
     * positive number leaves that alone, which is the whole reason the question can be canonicalised
     * at all. It is everything to a question about where the form runs: {@code 2a - 2b} runs twice as
     * far as {@code a - b}, and an answer about the second handed back for the first is out by a
     * factor with nothing to say it is.
     */
    private record Asked<A>(Goal<A> goal, ExactRatio by) {}

    /**
     * A question, in the one form every way of asking it comes to.
     *
     * <p>The rules were being canonicalised on the way in and the questions were not, so
     * {@code 2x + 2y <= 10} and {@code x + y <= 5} — one question — were answered differently: the
     * rule kept is the second, and a premise is taken off a goal once, so the first was left with a
     * residual nothing could prove. The same thing reached the audit, where a difference asked as
     * {@code 2a - 2b <= 4} was not recognised as a difference at all and a rule the ranges do state
     * came back unstated.
     *
     * <p>Divided through by what the weights share, which is a positive number and so leaves which
     * side of nought the question is about.
     */
    private Asked<A> goalOf(LinearForm<A> f) {
        Map<A, ExactRatio> coefs = weighed(f);
        ExactRatio constant = f.constant();
        // Canonicalised by the one thing that canonicalises, so a question and a rule that say the
        // same thing are put into the same words by the same code. Doing the division here instead
        // would be a second account of what one rule is — which is the thing being removed.
        return switch (CanonicalForm.of(coefs)) {
            case CanonicalForm.NoTerms<A> _ ->
                    new Asked<>(new Goal<>(Map.of(), constant), ExactRatio.ONE);
            case CanonicalForm.Unheld<A> _ -> null;
            case CanonicalForm.Scaled<A> scaled -> switch (constant.dividedBy(scaled.by())) {
                case ExactAnswer.Held<ExactRatio> held ->
                        new Asked<>(new Goal<>(scaled.form().coefs(), held.value()), scaled.by());
                case ExactAnswer.Unheld<ExactRatio> _ -> null;
            };
        };
    }

    /**
     * Whether {@code Σ c·x + k <= 0} (or {@code < 0}) follows.
     *
     * <p>Which is a question about how high the goal reaches, and nothing here answers that. What
     * the routes are and how many rules one of them may take are {@link FormReach}'s, said there
     * once. A second account of them beside this method is a second thing to keep true, and the one
     * that stood here had gone on saying the residual is bounded by the ranges alone after the
     * relations had been added to it.
     */
    private boolean proves(Goal<A> goal, boolean strict, boolean withRules) {
        ExactCut highest = highestProven(goal, withRules);
        if (highest == null) {
            return false;
        }
        int sign = highest.at().signum();
        // An end at nought the goal cannot reach proves the strict form: nothing the rules admit
        // gets there, which is what `< 0` asks.
        return sign < 0 || (sign == 0 && (!strict || !highest.inclusive()));
    }

    /**
     * The highest the goal comes to, or null where nothing bounds it above.
     *
     * <p><b>Read in one place and derived in another.</b> {@link #boundsOf(LinearForm)},
     * {@link #entails} and {@link #refutes} all come here, so what a form is said to run up to and
     * what is said to follow from it are one statement. They had not been: the ranges said
     * {@code x + y} ran to ten while the proof beside them showed {@code x + y <= 5} — both sound,
     * and not the same abstract state, which is the shape all of this exists to remove.
     *
     * <p>What the derivation is belongs to {@link FormReach}, and it is not this class's because it
     * is not only this class's question: a rule being reduced asks it of the rest of its own form,
     * and the two readings had come apart in exactly the way the ranges and the proof once had. The
     * routes, and how many rules one of them may take, are said there and read from here.
     *
     * @param withRules false to ask what the ends and the closed relations between them say, leaving
     *                  the rules beside them out. A different question from what the rules say, and
     *                  the one an account of what was derived wants — and not the product of the
     *                  ranges either, which holds less than this does
     */
    private ExactCut highestProven(Goal<A> goal, boolean withRules) {
        FormReach<A> reading = reading();
        return withRules
                ? reading.most(goal.coefs(), goal.constant())
                : reading.mostFromTheEndsAndTheDifferences(goal.coefs(), goal.constant());
    }

    /** The one reading of what the rules leave a form, over the state they have been worked out to. */
    private FormReach<A> reading() {
        ClosedState<A> state = closed();
        return FormReach.over(rules(), state.box(), state.differences(), order);
    }


    // --- reading the domain back --------------------------------------------------------------------

    /**
     * The tightest bounds the rules prove on one atom, {@code null} at either end where they prove
     * none.
     *
     * <p>Everything the rules say and not what was written down about the atom alone: a difference
     * carries a bound from another position, and a rule over several positions leaves each of them
     * whatever the others cannot help taking. That is the whole point of asking here rather than
     * reading back what was put in.
     *
     * <p><b>What was proven and not where a value may be put.</b> A reading that admits no
     * assignment still has ends written down, and reading them back is how a refusal names the
     * position whose ends crossed. A caller choosing somewhere for a value to stand is asking the
     * other question, and the pair of nulls this hands back on such a reading is the widest answer
     * there is: {@link #projectionOf(Object)} is that question, and it has the answer this has no
     * room for.
     */
    public Bounds boundsOf(A atom) {
        if (isBottom()) {
            return new Bounds(null, null);
        }
        Box<A> box = closed().box();
        return new Bounds(written(box.leastOf(atom), false), written(box.mostOf(atom), true));
    }

    /**
     * What this domain says about where one atom's values lie, for a reader meeting it with an
     * answer of its own.
     *
     * <p>Three answers, because {@link Bounds} alone cannot tell them apart. A rule naming an atom
     * and narrowing neither end leaves the same pair of nulls as an atom no rule ever mentioned, and
     * the two say opposite things to whoever is meeting them: the first is this domain speaking and
     * placing no edge, the second is this domain having nothing to say at all. Which of them it is
     * is {@link #atomsSpokenOf}'s answer and is not readable off the ends.
     *
     * <p>And the rules holding nothing is neither. An atom of a domain that admits no assignment is
     * not at every value, which is what a pair of nulls would say; there is no value for it to be
     * at. Said as {@link Projection.NothingIsLeft}, so that a caller cannot reach a range out of a
     * domain whose rules contradict — read as open, it would widen whatever it was met with and the
     * contradiction would leave with it.
     */
    public Projection projectionOf(A atom) {
        if (isBottom()) {
            return new Projection.NothingIsLeft();
        }
        return kinds.contains(atom)
                ? new Projection.Within(boundsOf(atom)) : new Projection.NotSpokenOf();
    }

    /** What a domain says about one atom: nothing, where its values lie, or that it has none. */
    public sealed interface Projection {

        /** No rule here names the atom, so nothing about it follows from these rules. */
        record NotSpokenOf() implements Projection {}

        /** The rules name it and prove it lies here — which is every value where they place no
         *  edge. */
        record Within(Bounds bounds) implements Projection {}

        /** The rules admit no assignment at all, so the atom is at no value rather than at any. */
        record NothingIsLeft() implements Projection {}
    }

    /**
     * What this domain says about where a form's values lie.
     *
     * <p>Two answers and not the three an atom gets. Whether an atom was ever named is a fact about
     * the vocabulary and is worth telling a reader; a form is several atoms, and whether it was
     * "named" would have to be invented — every term spoken of, or any of them — for a difference no
     * reader of a form asks about. What a form is owed is the one that changes the answer: a form
     * over a reading that admits no assignment is at no value, and a pair of nulls says it is at
     * every one.
     */
    public FormProjection projectionOf(LinearForm<A> f) {
        return isBottom() ? new FormProjection.NothingIsLeft()
                : new FormProjection.Within(boundsOf(f));
    }

    /** What a domain says about a form: where its values lie, or that it has none. */
    public sealed interface FormProjection {

        /** The rules prove it lies here — which is every value where they place no edge. */
        record Within(Bounds bounds) implements FormProjection {}

        /** The rules admit no assignment at all, so the form is at no value rather than at any. */
        record NothingIsLeft() implements FormProjection {}
    }

    /**
     * The tightest bounds the rules prove on a whole form.
     *
     * <p>Read for a value the rules cannot carry directly: a product of two positions and a
     * truncating quotient are outside what this reasons in, and what they answer is bounded by what
     * their parts are proven to lie between.
     *
     * <p>What was proven, as the one above is, and {@link #projectionOf(LinearForm)} is where a
     * caller looking for somewhere to put a value asks.
     */
    public Bounds boundsOf(LinearForm<A> f) {
        if (isBottom()) {
            return new Bounds(null, null);
        }
        Asked<A> asked = goalOf(f);
        if (asked == null) {
            // A form whose lowest terms have no representation is one nothing here can bound.
            return new Bounds(null, null);
        }
        ExactCut highest = highestProven(asked.goal(), true);
        ExactCut lowest = highestProven(asked.goal().negated(), true);
        // Back into the units the caller asked in. The question was answered about the form divided
        // through by what its weights share, and the caller wants the form it wrote.
        return new Bounds(
                lowest == null ? null : written(
                        backInto(lowest.at().negated(), asked.by(), lowest.inclusive()), false),
                highest == null ? null : written(
                        backInto(highest.at(), asked.by(), highest.inclusive()), true));
    }

    /** A cut scaled back by {@code by}, or {@code null} where the scaled value has no
     *  representation — no end, which is what an unbounded end already means to every reader. */
    private static ExactCut backInto(ExactRatio at, ExactRatio by, boolean inclusive) {
        ExactRatio scaled = at.times(by).orNull();
        return scaled == null ? null : new ExactCut(scaled, inclusive);
    }

    /**
     * A cut as a number somebody can write.
     *
     * <p>The one place the exact arithmetic stops. Almost every bound is already a decimal — one on a
     * position whose values step is a whole number — and a bound at a value like a third is not, so
     * it is written out to as many digits as it takes and rounded the way that widens. What is handed
     * over then admits everything the rules admit and a hair besides, which is the safe direction: a
     * reader refusing a value the rules leave is the failure nothing downstream can see.
     */
    private Endpoint written(ExactCut cut, boolean upper) {
        if (cut == null) {
            return null;
        }
        // A decimal the host has no room to write out is an end this cannot hand over, and the sound
        // answer with less is no end here for the reason below. It is not the answer that no decimal
        // is this number, which would send it to the rounding: that one is about the number, and
        // this is about the run.
        ExactAnswer<Optional<BigDecimal>> exactly = cut.at().writtenDecimal();
        if (exactly instanceof ExactAnswer.Unheld<Optional<BigDecimal>>) {
            return null;
        }
        Optional<BigDecimal> written = ((ExactAnswer.Held<Optional<BigDecimal>>) exactly).value();
        if (written.isPresent()) {
            return new Endpoint(new Count(written.get()), cut.inclusive());
        }
        // Rounded outward, so that what is handed over admits everything the rules admit and a hair
        // besides. Where the exact arithmetic cannot hold that rounding either — an end this compiler
        // derived standing at the far side of the scale range from where it rounds to — the sound
        // answer with less is no end here rather than a number that does not exist: null is what an
        // unbounded end already means to every reader of one.
        BigDecimal outward = cut.at().asDecimal(
                upper ? RoundingMode.CEILING : RoundingMode.FLOOR,
                DIGITS_WHEN_IT_IS_NOT_A_DECIMAL).orNull();
        return outward == null ? null : new Endpoint(new Count(outward), true);
    }

    /**
     * Every atom this domain says anything about.
     *
     * <p>What it is for is the other side of it: an atom outside this is one no question asked here
     * can reach, so asserting something about it cannot change what is proven about anything else.
     * Generous where it is uncertain — an atom named in a rule that narrows nothing is still here,
     * because it is one a rule was written about.
     */
    public Set<A> atomsSpokenOf() {
        return kinds.keys();
    }

    /**
     * How the values of {@code atom} are spaced here, or null where nothing said.
     *
     * <p>Asked by a reader counting the values between two ends, which only a spacing makes a number:
     * the same pair of ends holds finitely many whole numbers and unboundedly many of anything
     * denser. Read off what was recorded rather than off the ends, because ends that happen to be
     * whole are what a dense value between two of them has as well.
     */
    public Granularity spacingOf(A atom) {
        return kinds.get(atom);
    }

    /**
     * A run of {@code atom} every value of which, at its own spacing, the rules leave it — or null
     * where that is not shown.
     *
     * <p>Not what {@link #projectionOf} answers, which is where the values lie and may be wider:
     * three things are shown of it together, and the run is answered with them rather than beside
     * them so that a caller cannot take one answer for another. The rules are shown to leave the
     * atom the whole of its run ({@link #leavesTheWholeOfItsRun}). Its ends are the
     * rules' own and not rounded past them: an end at a third is handed over as a decimal a hair
     * below, which no value of the atom is ({@link #endsAreWrittenExactly}). And each end is one
     * the atom takes: a whole number at or inside a strict end where the values step by one, and
     * an end that is not taken only where they are dense, so that some value lies as near it as any
     * other value asked of. An atom whose spacing nothing recorded is a value the arithmetic does
     * not count, and no run of it is shown.
     *
     * <p>A row is values the atoms' orders hold, and a point of the rules past where an order
     * stops is no row: {@code a - b >= M} beside {@code b >= 1}, the greatest {@code Int} at
     * {@code M}, holds only an {@code a} past it. So whether the rules leave any row is asked
     * inside where each atom's order stops, as this domain was told it
     * ({@link #heldInsideTheirOrders}), and a system with an atom it was not told of is not shown
     * to leave one: no point of it is known to be a row. The run answered is the rules' own and
     * runs on past an order's end as before; a caller reads that end as the order it is counted
     * on says.
     */
    public Bounds wholeRunOf(A atom) {
        if (!leavesTheWholeOfItsRun(atom) || !endsAreWrittenExactly(atom)
                || !(projectionOf(LinearForm.atom(atom)) instanceof FormProjection.Within(
                        Bounds run))) {
            return null;
        }
        return switch (spacingOf(atom)) {
            case null -> null;
            case DENSE -> run;
            case DISCRETE -> onWholeNumbers(run);
        };
    }

    /**
     * Whether the rules are shown to leave {@code atom} the whole of its run: what
     * {@link #projectionCertification} asks of every rule, asked of the rules a chain of them
     * relates to the atom, and of the rest only that they leave some value.
     *
     * <p>Positions no chain of rules relates to the atom are another system written beside its
     * own, which bounds nothing of it but whether any value is left at all. So such a system is
     * shown to hold a value inside where its atoms' orders stop: by the box and its differences
     * where they prove each of its rules, those ends taken in, and otherwise by a point of its
     * box inside those ends each of its rules holds at ({@link #aPointOfTheBoxHolds}). The atom's
     * own system is proven so too. {@code 4h - 3s < 0} over two decimals running nought to 168 is
     * no difference and is not proven, and leaves a whole number apart from both the whole of its
     * run, since {@code h} at nought and {@code s} at 168 hold it. A system of boxes and limits on
     * sums ({@code a + b <= M}) leaves each atom the whole of its run too, with the others at the
     * low corner of their boxes ({@link #limitsOnSumsHoldAtTheLowCorner}).
     *
     * <p>What each system is shown to be is the domain's alone, worked out where an atom first
     * asks it and kept for every other atom, and asked no further than the first system that
     * keeps the run from being shown.
     */
    private boolean leavesTheWholeOfItsRun(A atom) {
        Systems<A> had = systems;
        if (had == null) {
            had = systemsOf();
            systems = had;
        }
        if (!had.anyShown()) {
            return false;
        }
        A its = had.groupOf().get(atom);
        if (its != null && shownOf(had, its) != Shown.PROVEN
                && shownOf(had, its) != Shown.AT_THE_LOW_CORNER) {
            return false;
        }
        for (A group : had.rulesOf().keySet()) {
            if (!group.equals(its) && shownOf(had, group) == Shown.NOTHING) {
                return false;
            }
        }
        return true;
    }

    /** What one system of the rules is shown to leave inside where its atoms' orders stop: its
     *  runs whole, its runs whole as limits on sums hold at the low corner of the box
     *  ({@link #limitsOnSumsHoldAtTheLowCorner}), some point, or neither shown. */
    private enum Shown { PROVEN, AT_THE_LOW_CORNER, A_POINT, NOTHING }

    /** What the system of {@code group} is shown to leave, worked out once. */
    private Shown shownOf(Systems<A> systems, A group) {
        return systems.shown().computeIfAbsent(group, key -> {
            List<A> atoms = systems.atomsOf().getOrDefault(key, List.of());
            List<AffineConstraint<A>> rules = systems.rulesOf().get(key);
            if (!atoms.stream().allMatch(orders::contains)) {
                return Shown.NOTHING;
            }
            if (systems.spacedAlike().contains(key)
                    && rules.stream().allMatch(rule -> proven(rule, false))) {
                return leavesAValueInside(atoms) ? Shown.PROVEN : Shown.NOTHING;
            }
            Map<A, Bounds> runs = runsInsideTheirOrders(atoms);
            if (runs != null && limitsOnSumsHoldAtTheLowCorner(atoms, runs, rules)) {
                return Shown.AT_THE_LOW_CORNER;
            }
            if ((runs != null && aPointOfTheBoxHolds(atoms, runs, rules))
                    || anOpenSetOfDecimalsIsLeft(atoms, rules)) {
                return Shown.A_POINT;
            }
            return Shown.NOTHING;
        });
    }

    /**
     * What each of {@code atoms} runs over inside where its order stops, or null where one has no
     * run that holds a value or no spacing recorded.
     */
    private Map<A, Bounds> runsInsideTheirOrders(List<A> atoms) {
        Map<A, Bounds> runs = new LinkedHashMap<>();
        for (A atom : atoms) {
            Bounds box = boxOf(atom);
            Bounds run = box == null ? null : box.meet(orders.get(atom));
            if (run == null || !run.holdsAValue() || spacingOf(atom) == null) {
                return null;
            }
            runs.put(atom, run);
        }
        return runs;
    }

    /** The pairs of bounds put together in asking whether a system of decimals leaves a point. */
    private static final long PAIRS_ASKED_OF_A_SYSTEM = 4096;

    /**
     * Whether the rules over decimals leave a point inside where the orders of {@code atoms} stop,
     * because they leave an open set: each bound taken strictly still leaves rational values
     * ({@link LaterNumbersEliminated}), and a set open in every direction holds a point whose
     * every coordinate is a finite decimal. A value held off a number leaves such a set a point,
     * and an equality leaves it none, so a system with one is not asked.
     *
     * <p>No value is picked inside a run: what is asked is whether the bounds meet, and the
     * elimination answers that for every system its pairs allow.
     */
    private boolean anOpenSetOfDecimalsIsLeft(List<A> atoms, List<AffineConstraint<A>> rules) {
        List<LaterNumbersEliminated.Bound<A>> bounds = new ArrayList<>();
        for (AffineConstraint<A> rule : rules) {
            switch (rule) {
                case AffineConstraint.HalfSpace<A> half -> {
                    Map<A, ExactRatio> weighed = new LinkedHashMap<>();
                    for (Map.Entry<A, ExactRatio> each : half.form().entriesIn(order)) {
                        weighed.put(each.getKey(), each.getValue());
                    }
                    bounds.add(new LaterNumbersEliminated.Bound<>(
                            new LinearForm<>(half.bound().at().negated(), weighed), true));
                }
                case AffineConstraint.Disequality<A> _ -> { }
                case AffineConstraint.Equality<A> _ -> {
                    return false;
                }
            }
        }
        for (A atom : atoms) {
            Bounds order = orders.get(atom);
            if (spacingOf(atom) != Granularity.DENSE || order == null) {
                return false;
            }
            if (order.min() != null) {
                if (!(order.min().at() instanceof Count least)) {
                    return false;
                }
                bounds.add(new LaterNumbersEliminated.Bound<>(new LinearForm<>(least.exactly(),
                        Map.of(atom, ExactRatio.ONE.negated())), true));
            }
            if (order.max() != null) {
                if (!(order.max().at() instanceof Count most)) {
                    return false;
                }
                bounds.add(new LaterNumbersEliminated.Bound<>(new LinearForm<>(
                        most.exactly().negated(), Map.of(atom, ExactRatio.ONE)), true));
            }
        }
        return LaterNumbersEliminated.of(bounds, atoms, PAIRS_ASKED_OF_A_SYSTEM)
                instanceof LaterNumbersEliminated.Eliminated<A>;
    }

    /**
     * Whether the rules over {@code atoms} are boxes and limits on sums that the least ends of
     * the atoms' runs, inside where their orders stop, leave some point of.
     *
     * <p>A limit on a sum is a half-space every weight of which is positive: lowering an atom
     * keeps it held. So with each atom but one at its least, the one is held at every value up to
     * the greatest the limits leave it, and that greatest is the end the closure answers for it.
     * What stands the others is their least end and nothing near it: a whole-numbered atom takes
     * its least whole number, and a decimal's least end is a value it takes only where the run
     * holds it. A limit the least ends meet exactly is held only where every atom it weighs takes
     * its least end, and one they pass is held by values as near the ends as asked. No value is
     * picked inside a run left open.
     */
    private boolean limitsOnSumsHoldAtTheLowCorner(List<A> atoms, Map<A, Bounds> runs,
                                                   List<AffineConstraint<A>> rules) {
        Map<A, ExactRatio> least = new LinkedHashMap<>();
        Set<A> taken = new LinkedHashSet<>();
        for (A atom : atoms) {
            Bounds run = runs.get(atom);
            Granularity spacing = spacingOf(atom);
            ExactRatio end = spacing == Granularity.DISCRETE
                    ? run.aValueNearestItsEnd(false, spacing)
                    : run.min() != null && run.min().at() instanceof Count count ? count.exactly()
                            : null;
            if (end == null) {
                return false;
            }
            least.put(atom, end);
            if (spacing == Granularity.DISCRETE || run.min().inclusive()) {
                taken.add(atom);
            }
        }
        for (AffineConstraint<A> rule : rules) {
            if (!(rule instanceof AffineConstraint.HalfSpace<A> half)) {
                return false;
            }
            if (weighedAtoms(half) <= 1) {
                continue;
            }
            ExactRatio sum = ExactRatio.ZERO;
            boolean everyAtomTakesItsLeast = true;
            for (Map.Entry<A, ExactRatio> each : half.form().coefs().entrySet()) {
                if (each.getValue().signum() < 0) {
                    return false;
                }
                if (!each.getValue().isZero()) {
                    ExactRatio weighed = least.get(each.getKey()).times(each.getValue()).orNull();
                    sum = weighed == null || sum == null ? null : sum.plus(weighed).orNull();
                    everyAtomTakesItsLeast &= taken.contains(each.getKey());
                }
            }
            if (sum == null) {
                return false;
            }
            int order = sum.compareTo(half.bound().at());
            if (order > 0 || (order == 0 && !(half.bound().inclusive() && everyAtomTakesItsLeast))) {
                return false;
            }
        }
        return true;
    }

    private static <A> long weighedAtoms(AffineConstraint.HalfSpace<A> half) {
        return half.form().coefs().values().stream().filter(weight -> !weight.isZero()).count();
    }

    /**
     * Whether the rules, proven by the box and its differences, leave a value inside where the
     * orders of {@code atoms} stop: where every box lies inside its atom's order, the closure
     * holding something already says so; otherwise the ends are taken in and asked again.
     *
     * <p>Only of a system every rule of which the box and its differences prove, over atoms spaced
     * alike ({@link #shownOf}). A state not shown empty is not a state with a value in it
     * ({@link #isBottom}), and it is one here because of those two. Proven, the rules say no more
     * than the closure does, so what the closure holds the rules hold; spaced alike, the
     * differences close exactly over the atoms. An end taken in bounds one atom, which keeps the
     * rules of that shape, so the closure with the ends in is still all they say. Asked of rules
     * the box and its differences do not prove, a closure wider than they are would be read as a
     * value of them.
     */
    private boolean leavesAValueInside(List<A> atoms) {
        NumericDomain<A> inside = insideTheOrdersOf(atoms);
        return inside != null && !inside.isBottom();
    }

    /**
     * Whether the rules leave no row: nothing at all, or nothing inside where the orders this
     * domain was told of stop ({@link #heldInsideTheirOrders}).
     *
     * <p>True is a proof, as {@link #isBottom} is: a row holds each number inside its order, so
     * rules that leave nothing there leave a row nothing. {@code b >= 1} beside
     * {@code a - b >= M}, the greatest {@code Int} at {@code M}, leaves a point and no row. False
     * is not a proof of a row. Asked apart from {@link #isBottom} and not put into the rules,
     * since what the rules leave is read as the model's own lines, and an order's end is none of
     * them.
     */
    public boolean leavesNoRow() {
        if (isBottom()) {
            return true;
        }
        Boolean had = noRow;
        if (had == null) {
            NumericDomain<A> inside = insideTheOrdersOf(
                    kinds.keys().stream().filter(orders::contains).toList());
            had = inside != this && inside != null && inside.isBottom();
            noRow = had;
        }
        return had;
    }

    /**
     * These rules with where the order of each of {@code atoms} stops taken in as its ends, or
     * this domain where every box already lies inside them — or null where an atom to be held
     * inside has no spacing to hold it by. An atom whose box lies inside its order is held there
     * already, so its ends add nothing the closure does not hold.
     */
    private NumericDomain<A> insideTheOrdersOf(List<A> atoms) {
        NumericDomain<A> inside = this;
        for (A atom : atoms) {
            Bounds stop = orders.get(atom);
            Bounds box = boxOf(atom);
            if (box != null && box.liesWithin(stop)) {
                continue;
            }
            if (spacingOf(atom) == null) {
                return null;
            }
            Map<A, Granularity> spaced = Map.of(atom, spacingOf(atom));
            if (stop.min() != null && stop.min().at() instanceof Count least) {
                inside = inside.assume(LinearForm.atomMinusConstant(atom, least.exactly()),
                        stop.min().inclusive() ? Rel.GE : Rel.GT, spaced);
            }
            if (stop.max() != null && stop.max().at() instanceof Count most) {
                inside = inside.assume(LinearForm.atomMinusConstant(atom, most.exactly()),
                        stop.max().inclusive() ? Rel.LE : Rel.LT, spaced);
            }
        }
        return inside;
    }

    /** Where the rules leave {@code atom}, or null where they leave it no run of numbers. */
    private Bounds boxOf(A atom) {
        return projectionOf(LinearForm.atom(atom)) instanceof FormProjection.Within(
                Bounds within) ? within : null;
    }

    /**
     * The systems the rules are in, each by its group, and what each is shown to leave, as far as
     * it has been asked.
     *
     * @param anyShown    whether a run is shown of any atom: not where nothing is left, the closure
     *                    is incomplete or a rule over no atom is not proven
     * @param groupOf     the group each atom a rule names is in
     * @param atomsOf     the atoms of each group
     * @param rulesOf     the rules of each group
     * @param spacedAlike the groups whose atoms are spaced alike
     * @param shown       what each system asked of is shown to leave
     */
    private record Systems<A>(boolean anyShown, Map<A, A> groupOf, Map<A, List<A>> atomsOf,
                              Map<A, List<AffineConstraint<A>>> rulesOf, Set<A> spacedAlike,
                              Map<A, Shown> shown) {

        static <A> Systems<A> none() {
            return new Systems<>(false, Map.of(), Map.of(), Map.of(), Set.of(),
                    new ConcurrentHashMap<>());
        }

        Systems {
            groupOf = Map.copyOf(groupOf);
            atomsOf = Map.copyOf(atomsOf);
            rulesOf = Collections.unmodifiableMap(new LinkedHashMap<>(rulesOf));
            spacedAlike = Set.copyOf(spacedAlike);
        }
    }

    private Systems<A> systemsOf() {
        if (isBottom() || !closed().everyBoundWasComposed()) {
            return Systems.none();
        }
        Map<A, A> reaches = related();
        Map<A, List<AffineConstraint<A>>> byGroup = new LinkedHashMap<>();
        for (AffineConstraint<A> rule : rules()) {
            List<A> atoms = rule.form().atomsIn(order);
            if (atoms.isEmpty()) {
                if (!proven(rule, false)) {
                    return Systems.none();
                }
                continue;
            }
            byGroup.computeIfAbsent(groupOf(reaches, atoms.getFirst()), _ -> new ArrayList<>())
                    .add(rule);
        }
        Map<A, A> groups = new LinkedHashMap<>();
        Map<A, List<A>> atomsOf = new LinkedHashMap<>();
        for (A each : List.copyOf(reaches.keySet())) {
            A group = groupOf(reaches, each);
            groups.put(each, group);
            atomsOf.computeIfAbsent(group, _ -> new ArrayList<>()).add(each);
        }
        Set<A> alike = new LinkedHashSet<>();
        for (Map.Entry<A, List<A>> group : atomsOf.entrySet()) {
            if (spacedAlike(reaches, group.getValue())) {
                alike.add(group.getKey());
            }
        }
        Map<A, List<A>> atoms = new LinkedHashMap<>();
        atomsOf.forEach((group, each) -> atoms.put(group, List.copyOf(each)));
        Map<A, List<AffineConstraint<A>>> rules = new LinkedHashMap<>();
        byGroup.forEach((group, each) -> rules.put(group, List.copyOf(each)));
        return new Systems<>(true, groups, atoms, rules, alike, new ConcurrentHashMap<>());
    }

    /**
     * Whether some point of the box over {@code atoms}, inside where each atom's order stops,
     * holds each of {@code rules}: for one of their half-spaces, each atom it weighs at the value
     * of its run nearest the end that takes the sum lowest, and each other at the value of its run
     * nearest nought ({@link Bounds#aValueNearestItsEnd}, {@link Bounds#aValueNearestNought}). An
     * atom whose run has no end that way is moved instead, once the rest stand, to a whole number
     * past where the half-space holds. Tried for each half-space in turn. Every value the point
     * stands at is one its atom takes inside its run.
     */
    private boolean aPointOfTheBoxHolds(List<A> atoms, Map<A, Bounds> runs,
                                        List<AffineConstraint<A>> rules) {
        for (AffineConstraint<A> rule : rules) {
            for (AffineConstraint.HalfSpace<A> half : rule.halfSpaces()) {
                Map<A, ExactRatio> point = new LinkedHashMap<>();
                A moved = null;
                for (A atom : atoms) {
                    Bounds run = runs.get(atom);
                    ExactRatio weight = half.form().coefs().get(atom);
                    boolean weighed = weight != null && !weight.isZero();
                    boolean greatest = weighed && weight.signum() < 0;
                    ExactRatio at = weighed ? run.aValueNearestItsEnd(greatest, spacingOf(atom))
                            : null;
                    if (at == null && weighed && moved == null
                            && (greatest ? run.max() == null : run.min() == null)) {
                        moved = atom;
                    }
                    at = at == null ? run.aValueNearestNought(spacingOf(atom)) : at;
                    if (at == null) {
                        break;
                    }
                    point.put(atom, at);
                }
                if (point.size() != atoms.size()) {
                    continue;
                }
                if (moved != null && !holdsAt(half, point)) {
                    ExactRatio to = pastWhereItHolds(half, point, moved);
                    if (to == null || !runs.get(moved).admits(to)) {
                        continue;
                    }
                    point.put(moved, to);
                }
                if (rules.stream().allMatch(each -> holdsAt(each, point))) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The whole number one past where {@code half} holds with every atom but {@code atom} at its
     * value in {@code point}: the rest's sum taken from the bound, over the atom's weight, and
     * stepped one further — or null where that is no number.
     */
    private static <A> ExactRatio pastWhereItHolds(AffineConstraint.HalfSpace<A> half,
                                                   Map<A, ExactRatio> point, A atom) {
        ExactRatio rest = ExactRatio.ZERO;
        for (Map.Entry<A, ExactRatio> each : half.form().coefs().entrySet()) {
            if (!each.getKey().equals(atom)) {
                ExactRatio weighed = point.get(each.getKey()).times(each.getValue()).orNull();
                rest = weighed == null || rest == null ? null : rest.plus(weighed).orNull();
            }
        }
        ExactRatio weight = half.form().coefs().get(atom);
        ExactRatio at = rest == null ? null
                : half.bound().at().minus(rest).flatMap(left -> left.dividedBy(weight)).orNull();
        if (at == null) {
            return null;
        }
        return weight.signum() > 0
                ? at.floor().map(whole -> ExactRatio.of(whole.subtract(BigInteger.ONE))).orNull()
                : at.ceiling().map(whole -> ExactRatio.of(whole.add(BigInteger.ONE))).orNull();
    }

    /** Whether {@code rule} holds with each of its atoms at its value in {@code point}. */
    private static <A> boolean holdsAt(AffineConstraint<A> rule, Map<A, ExactRatio> point) {
        ExactRatio sum = ExactRatio.ZERO;
        for (Map.Entry<A, ExactRatio> each : rule.form().coefs().entrySet()) {
            ExactRatio at = point.get(each.getKey());
            ExactRatio weighed = at == null ? null : at.times(each.getValue()).orNull();
            sum = weighed == null || sum == null ? null : sum.plus(weighed).orNull();
        }
        if (sum == null) {
            return false;
        }
        return switch (rule) {
            case AffineConstraint.HalfSpace<A> half -> {
                int order = sum.compareTo(half.bound().at());
                yield order < 0 || (order == 0 && half.bound().inclusive());
            }
            case AffineConstraint.Equality<A> at -> sum.compareTo(at.at()) == 0;
            case AffineConstraint.Disequality<A> hole -> sum.compareTo(hole.at()) != 0;
        };
    }

    /** {@code run} with each end the whole number nearest it that the run takes — or null where
     *  an end is no number this can step from. An absent end, which runs to the end of the type,
     *  is kept absent. */
    private static Bounds onWholeNumbers(Bounds run) {
        Endpoint low = run.min() == null ? null : wholeAt(run.min(), true);
        Endpoint high = run.max() == null ? null : wholeAt(run.max(), false);
        if ((run.min() != null && low == null) || (run.max() != null && high == null)) {
            return null;
        }
        return new Bounds(low, high);
    }

    /**
     * The whole number nearest {@code end} on the run's side of it that the run takes.
     *
     * @return null where the end is no number this can step from
     */
    private static Endpoint wholeAt(Endpoint end, boolean least) {
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        ExactRatio at = count.exactly();
        ExactAnswer<BigInteger> stepped = least ? at.ceiling() : at.floor();
        if (!(stepped instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))) {
            return null;
        }
        BigInteger taken = end.inclusive() || !ExactRatio.of(whole).equals(at) ? whole
                : least ? whole.add(BigInteger.ONE) : whole.subtract(BigInteger.ONE);
        return Endpoint.inclusive(Count.of(new BigDecimal(taken)));
    }

    /** What an atom's values are known to lie between. A {@code null} end is unbounded there. */
    public record Bounds(Endpoint min, Endpoint max) {

        /** Neither end written down, which is every value there is. Beside
         * {@link OrderedInterval#OPEN} and the same thing said of this pair: a caller with nothing
         * to say says it with this rather than with a {@code null} that a reader has to tell from
         * one meaning something else. */
        public static final Bounds OPEN = new Bounds(null, null);

        /**
         * Whether neither end was written down, which is a range of every value there is.
         *
         * <p>Called {@code isEmpty} until {@link #holdsAValue} stood beside it, where the two names
         * said opposite things about the same range: a range with neither end holds every value, and
         * one that holds none of them has both. What is empty here is the pair of ends and never the
         * range.
         */
        public boolean saysNothing() {
            return min == null && max == null;
        }

        /**
         * Whether this holds any value at all.
         *
         * <p>Not {@link #saysNothing}, which asks whether either end was written down. A range with
         * neither end says nothing and holds everything; a range whose ends have crossed says two
         * things and holds nothing.
         */
        public boolean holdsAValue() {
            return Endpoint.someValueLiesBetween(min, max);
        }

        /**
         * The one whole number both ends are written at, or null where the range holds more than
         * one value or an end is no whole number this reads.
         */
        public BigInteger holdsOneWholeNumber() {
            if (min == null || max == null || !min.inclusive() || !max.inclusive()
                    || !(min.at() instanceof Count low) || !(max.at() instanceof Count high)
                    || !low.exactly().equals(high.exactly()) || !low.exactly().isWhole()
                    || !(low.exactly().floor() instanceof ExactAnswer.Held<BigInteger> whole)) {
                return null;
            }
            return whole.value();
        }

        /** The values this and {@code other} both hold. Each end is the tighter of the two, which
         * for a lower bound is the higher and for an upper bound the lower. */
        public Bounds meet(Bounds other) {
            return new Bounds(Endpoint.lower(min, other.min), Endpoint.upper(max, other.max));
        }

        /**
         * These ends held to {@code wider}: nothing at all where the two share no value, and
         * otherwise each end this has no further out than {@code wider}'s.
         *
         * <p>Two questions, and the first is about the range and not about either end. An arithmetic
         * composed over numbers of any size can work out to values the thing it is about never
         * takes, and where none of them is one of {@code wider}'s the answer is that there is no
         * such value — which is a fact about the two ranges together. Asked end by end alone, a
         * range lying wholly past one side of {@code wider} keeps whichever end it has none of and
         * comes back holding values that were the reason to ask: everything above the largest whole
         * number is still everything above it once its lower end has been pulled down.
         *
         * <p>The second is {@link #meet} with one difference, and the difference is what it is for:
         * an end this has none of stays absent rather than taking {@code wider}'s. So this sharpens
         * the ends that are here and states none that are not — which is what a reader correcting an
         * answer wants, as against one adding a fact of its own.
         */
        public Bounds noFurtherOutThan(Bounds wider) {
            Bounds shared = meet(wider);
            if (!shared.holdsAValue()) {
                return shared;
            }
            return new Bounds(min == null ? null : Endpoint.lower(min, wider.min),
                    max == null ? null : Endpoint.upper(max, wider.max));
        }

        /** Whether {@code at} is inside both ends — asked of the ends, because whether an end is one
         * of the counts it stops at is what the number alone does not say. */
        public boolean admits(Place at) {
            return (min == null || Endpoint.someValueLiesBetween(min, Endpoint.inclusive(at)))
                    && (max == null || Endpoint.someValueLiesBetween(Endpoint.inclusive(at), max));
        }

        /**
         * The same asked of a number the algebra above this reasons in.
         *
         * <p><b>The ends come up here rather than the number going down.</b> This range is written
         * in what a carrier counts, because it is read off the declarations; what is being held
         * against it may be a number no carrier counts to — a quantity stepping by a third stands at
         * one. Every count is a ratio, so lifting an end loses nothing and the comparison is the one
         * it always was; writing the number as a count instead answers about a place it is not at,
         * or about no place at all.
         *
         * <p>Which is why this range needs no exact arithmetic of its own. It is an envelope over
         * what a row may hold, and an envelope says the same thing in either arithmetic.
         */
        public boolean admits(ExactRatio at) {
            return endAdmits(min, at, true) && endAdmits(max, at, false);
        }

        /** Whether one end lets {@code at} past it, which is the end's own strictness read against
         *  the lifted number. */
        private static boolean endAdmits(Endpoint end, ExactRatio at, boolean lower) {
            if (end == null) {
                return true;
            }
            int order = Count.number(end.at()).exactly().compareTo(at);
            return (lower ? order < 0 : order > 0) || (order == 0 && end.inclusive());
        }

        /**
         * The range holding everything either of these holds: the looser end on each side. An end
         * absent is every value that way, so it is what this answers with wherever either side has
         * none.
         *
         * <p>Not called a join, and {@link #meet} beside it is not called that either. A meet of two
         * ranges can hold nothing and this record says so with crossed ends rather than with a
         * bottom of its own, so a caller taking one asks {@link #holdsAValue} where it matters. This
         * one cannot: two ranges that each hold a value span a range that holds both.
         */
        public static Bounds spanning(Bounds a, Bounds b) {
            if (a.min() == null || b.min() == null) {
                return new Bounds(null, looserUpper(a, b));
            }
            Endpoint low = Endpoint.lower(a.min(), b.min()).equals(a.min()) ? b.min() : a.min();
            return new Bounds(low, looserUpper(a, b));
        }

        private static Endpoint looserUpper(Bounds a, Bounds b) {
            if (a.max() == null || b.max() == null) {
                return null;
            }
            return Endpoint.upper(a.max(), b.max()).equals(a.max()) ? b.max() : a.max();
        }

        /** Whether every value this holds is one {@code wider} holds. An end {@code wider} does not
         * have holds everything on that side, and an end this does not have is held only where
         * {@code wider} has none either. */
        public boolean liesWithin(Bounds wider) {
            return endHolds(min, wider.min(), true) && endHolds(max, wider.max(), false);
        }

        private static boolean endHolds(Endpoint mine, Endpoint wider, boolean low) {
            if (wider == null) {
                return true;
            }
            if (mine == null) {
                return false;
            }
            return (low ? Endpoint.lower(mine, wider) : Endpoint.upper(mine, wider)).equals(mine);
        }

        /**
         * Whether the values this holds stand {@code rel} to {@code against}: true where every one
         * of them does, false where none does, and null where some do and some do not.
         *
         * <p>The one answer to it for a range. Each relation is asked on its own terms rather than
         * through the range where its denial holds, because the values other than one are no one
         * range: asked that way, a range of just {@code against} could never be shown equal to it.
         */
        public Boolean stands(Rel rel, Count against) {
            if (everyValueStands(rel, against)) {
                return true;
            }
            return everyValueStands(rel.denied(), against) ? false : null;
        }

        /**
         * A value of {@code spacing} this holds nearest nought — or null where none is shown:
         * nought where this holds it, and otherwise the value nearest the end on nought's side
         * ({@link #aValueNearestItsEnd}).
         */
        public ExactRatio aValueNearestNought(Granularity spacing) {
            if (spacing == null) {
                return null;
            }
            if (admits(ExactRatio.ZERO)) {
                return ExactRatio.ZERO;
            }
            ExactRatio low = numberAt(min);
            return aValueNearestItsEnd(low == null || low.signum() < 0, spacing);
        }

        /**
         * The value of {@code spacing} this holds nearest its greatest end, for {@code greatest},
         * or its least — or null where that end is absent or no value is shown near it.
         *
         * <p>An end it holds is that value, where the spacing takes it. An end it leaves out is
         * passed by one step inward: the whole number past it, or a decimal one past it — or, where
         * the other end is nearer than one, the decimal halfway to that end. A value no decimal
         * writes is none a dense value takes, so an end at a third gives none here.
         */
        public ExactRatio aValueNearestItsEnd(boolean greatest, Granularity spacing) {
            Endpoint end = greatest ? max : min;
            ExactRatio at = numberAt(end);
            if (spacing == null || at == null) {
                return null;
            }
            int inward = greatest ? -1 : 1;
            ExactRatio taken = switch (spacing) {
                case DISCRETE -> (greatest ? at.floor() : at.ceiling())
                        .map(whole -> ExactRatio.of(whole)).orNull();
                case DENSE -> {
                    if (end.inclusive()) {
                        yield at;
                    }
                    ExactRatio other = numberAt(greatest ? min : max);
                    ExactRatio width = other == null ? null : other.minus(at).orNull();
                    ExactRatio step = width == null || width.abs().compareTo(ExactRatio.ONE) > 0
                            ? ExactRatio.ONE
                            : width.abs().dividedBy(ExactRatio.of(2)).orNull();
                    ExactRatio move = step == null ? null
                            : step.times(ExactRatio.of(inward)).orNull();
                    yield move == null ? null : at.plus(move).orNull();
                }
            };
            if (taken != null && spacing == Granularity.DISCRETE && !admits(taken)) {
                taken = taken.plus(ExactRatio.of(inward)).orNull();
            }
            return taken != null && admits(taken)
                    && (spacing != Granularity.DENSE || taken.fitsWrittenDecimal()) ? taken : null;
        }

        /** The number an end stands at, or null where there is no end or it is no number. */
        private static ExactRatio numberAt(Endpoint end) {
            return end != null && end.at() instanceof Count count ? count.exactly() : null;
        }

        private boolean everyValueStands(Rel rel, Count against) {
            return switch (rel) {
                case GE -> liesWithin(new Bounds(Endpoint.inclusive(against), null));
                case GT -> liesWithin(new Bounds(Endpoint.exclusive(against), null));
                case LE -> liesWithin(new Bounds(null, Endpoint.inclusive(against)));
                case LT -> liesWithin(new Bounds(null, Endpoint.exclusive(against)));
                case EQ -> liesWithin(new Bounds(Endpoint.inclusive(against),
                        Endpoint.inclusive(against)));
                case NE -> !admits(against);
            };
        }
    }

    /**
     * Whether both ends of {@code atom}'s range are numbers a model could write.
     *
     * <p>The one place the exact arithmetic stops, asked about. Almost every end is written exactly
     * — one on a position whose values step is a whole number — and an end at a value like a third
     * is not, so what is handed over is rounded past where the rules stop. Sound, and no longer the
     * rules' own edge, which is a thing a reader placing a row at an edge has to know.
     */
    public boolean endsAreWrittenExactly(A atom) {
        if (isBottom()) {
            return true;   // no ends are handed over, so none of them is rounded
        }
        Box<A> box = closed().box();
        return writtenExactly(box.leastOf(atom)) && writtenExactly(box.mostOf(atom));
    }

    private static boolean writtenExactly(ExactCut cut) {
        return cut == null || cut.at().fitsWrittenDecimal();
    }
}
