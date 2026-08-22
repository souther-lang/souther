package souther.compiler.numeric;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * {@code TotalityChecker}'s scope map. Constants are {@link BigDecimal} at the edges, because that is
 * what a carrier counts in and what a model writes; inside, the arithmetic is exact
 * ({@link Rational}), since dividing is what deriving a bound does and neither of those is closed
 * under it.
 */
public final class NumericDomain<A> {

    /** A comparison of a {@link LinearForm} against zero. */
    public enum Rel { GE, GT, LE, LT, EQ, NE }

    /** An affine form {@code const + Σ coef·atom} over the domain's atoms. */
    public record LinearForm<A>(BigDecimal constant, Map<A, BigDecimal> coefs) {
        public static <A> LinearForm<A> constant(BigDecimal c) {
            return new LinearForm<>(c, Map.of());
        }

        public static <A> LinearForm<A> atom(A a) {
            return new LinearForm<>(BigDecimal.ZERO, Map.of(a, BigDecimal.ONE));
        }

        public LinearForm<A> plus(LinearForm<A> o) {
            Map<A, BigDecimal> m = new HashMap<>(coefs);
            o.coefs.forEach((k, v) -> m.merge(k, v, BigDecimal::add));
            m.values().removeIf(v -> v.signum() == 0);
            return new LinearForm<>(constant.add(o.constant), m);
        }

        public LinearForm<A> negate() {
            Map<A, BigDecimal> m = new HashMap<>();
            coefs.forEach((k, v) -> m.put(k, v.negate()));
            return new LinearForm<>(constant.negate(), m);
        }

        public LinearForm<A> minus(LinearForm<A> o) {
            return plus(o.negate());
        }

        /** This form scaled by a constant {@code k} (a scalar multiply). */
        public LinearForm<A> times(BigDecimal k) {
            if (k.signum() == 0) {
                return constant(BigDecimal.ZERO);
            }
            Map<A, BigDecimal> m = new HashMap<>();
            coefs.forEach((key, v) -> m.put(key, v.multiply(k)));
            return new LinearForm<>(constant.multiply(k), m);
        }
    }

    /**
     * How many digits a bound is written out to where it is not a decimal at all.
     *
     * <p>Almost never reached. A bound on a position whose values step lands on a whole number, and
     * a bound on one whose values fill is usually a decimal too; what is left is a bound at a value
     * like a third, which no decimal is. Rounded outward when it happens, so what is handed over
     * still admits everything the rules admit.
     */
    private static final int DIGITS_WHEN_IT_IS_NOT_A_DECIMAL = 34;

    private final List<AffineConstraint<A>> rules;
    private final Map<A, Granularity> kinds;
    private final boolean readARuleNothingSatisfies;
    private ClosedState<A> closed;

    private NumericDomain(List<AffineConstraint<A>> rules, Map<A, Granularity> kinds,
                          boolean readARuleNothingSatisfies) {
        this.rules = rules;
        this.kinds = kinds;
        this.readARuleNothingSatisfies = readARuleNothingSatisfies;
    }

    public static <A> NumericDomain<A> top() {
        return new NumericDomain<>(List.of(), Map.of(), false);
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
        Map<A, Rational> coefs = new LinkedHashMap<>();
        f.coefs().forEach((atom, coef) -> coefs.put(atom, Rational.of(coef)));
        AffineConstraint.Read<A> read = AffineConstraint.of(
                coefs, Rational.of(f.constant()), rel, knowing.kinds::get);
        return switch (read) {
            // Nothing satisfies it, so nothing satisfies it together with anything else.
            case AffineConstraint.Read.HoldsNever<A> ignored ->
                    new NumericDomain<>(List.of(), knowing.kinds, true);
            // Every value satisfies it, so there is nothing to keep.
            case AffineConstraint.Read.HoldsAlways<A> ignored -> knowing;
            case AffineConstraint.Read.Stated<A> stated -> knowing.keeping(stated.constraint());
        };
    }

    /**
     * The domain with one more rule kept.
     *
     * <p>Kept and not merged into anything. A rule said twice is the same rule and the same key, so
     * the second saying adds nothing — which is what makes the answer a function of which rules were
     * said rather than of how often each was.
     */
    private NumericDomain<A> keeping(AffineConstraint<A> rule) {
        if (rules.contains(rule)) {
            return this;
        }
        List<AffineConstraint<A>> next = new ArrayList<>(rules);
        next.add(rule);
        return new NumericDomain<>(List.copyOf(next), kinds, false);
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
        LinearForm<A> form = LinearForm.atom(atom);
        NumericDomain<A> out = this;
        if (bounds.min() != null) {
            out = out.assume(form.minus(LinearForm.constant(Count.number(bounds.min().at()).at())),
                    bounds.min().inclusive() ? Rel.GE : Rel.GT, atomKinds);
        }
        if (bounds.max() != null) {
            out = out.assume(form.minus(LinearForm.constant(Count.number(bounds.max().at()).at())),
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
        Map<A, Granularity> next = null;
        for (A atom : atoms) {
            Granularity given = atomKinds.get(atom);
            if (given == null) {
                throw new IllegalStateException("no granularity given for atom `" + atom + "`");
            }
            Granularity had = kinds.get(atom);
            if (had == given) {
                continue;
            }
            if (had != null) {
                throw new IllegalStateException("atom `" + atom + "` is " + had + " and " + given);
            }
            if (next == null) {
                next = new HashMap<>(kinds);
            }
            next.put(atom, given);
        }
        return next == null ? this
                : new NumericDomain<>(rules, Map.copyOf(next), readARuleNothingSatisfies);
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
    public <B> NumericDomain<B> over(java.util.function.Function<A, B> naming) {
        // Settled once, over every position these rules speak of, which is what this holds and no
        // rule of it does. A rule asked whether a naming is one-to-one can only answer about its own
        // positions, so two independent rules would be carried across as two rules about one number
        // and a box holding something would come back holding nothing.
        Renaming<A, B> called = Renaming.of(kinds.keySet(), naming);
        Map<B, Granularity> spacing = new LinkedHashMap<>();
        kinds.forEach((atom, spaced) -> spacing.put(called.of(atom), spaced));
        List<AffineConstraint<B>> out = new ArrayList<>();
        for (AffineConstraint<A> rule : rules) {
            AffineConstraint<B> renamed = rule.over(called);
            if (!out.contains(renamed)) {
                out.add(renamed);
            }
        }
        return new NumericDomain<>(List.copyOf(out), Map.copyOf(spacing),
                readARuleNothingSatisfies);
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
     * <p>Spacings are checked rather than merged. Two readings calling one position by one name and
     * spacing it two ways is the naming and the typing disagreeing, and picking the safer of the two
     * would answer about a position neither reading was about.
     */
    public NumericDomain<A> meet(NumericDomain<A> other) {
        if (other == null || (other.rules.isEmpty() && other.kinds.isEmpty()
                && !other.readARuleNothingSatisfies)) {
            return this;
        }
        Map<A, Granularity> both = new LinkedHashMap<>(kinds);
        other.kinds.forEach((atom, spacing) -> {
            Granularity had = both.put(atom, spacing);
            if (had != null && had != spacing) {
                throw new IllegalStateException("atom `" + atom + "` is " + had + " and " + spacing);
            }
        });
        List<AffineConstraint<A>> out = new ArrayList<>(rules);
        for (AffineConstraint<A> rule : other.rules) {
            if (!out.contains(rule)) {
                out.add(rule);
            }
        }
        return new NumericDomain<>(List.copyOf(out), Map.copyOf(both),
                readARuleNothingSatisfies || other.readARuleNothingSatisfies);
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
        if (closed == null) {
            closed = ClosedState.of(rules, kinds::get);
        }
        return closed;
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
        if (!everyRelatedPositionIsSpacedAlike()) {
            return new ProjectionCertification.PositionsSpacedDifferently();
        }
        for (AffineConstraint<A> rule : rules) {
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
        Map<A, A> reaches = new LinkedHashMap<>();
        for (AffineConstraint<A> rule : rules) {
            A first = null;
            for (A atom : rule.form().coefs().keySet()) {
                if (first == null) {
                    first = atom;
                } else {
                    relate(reaches, first, atom);
                }
            }
        }
        Map<A, Granularity> ofGroup = new LinkedHashMap<>();
        for (A atom : List.copyOf(reaches.keySet())) {
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
        Map<A, Rational> coefs = weighed(f);
        if (!kinds.keySet().containsAll(coefs.keySet())) {
            // A position this has never been told about is one nothing here bounds, so nothing here
            // proves about it either. Said before the reading, which would want its spacing.
            return false;
        }
        return switch (AffineConstraint.of(coefs, Rational.of(f.constant()), rel, kinds::get)) {
            case AffineConstraint.Read.HoldsAlways<A> ignored -> true;
            case AffineConstraint.Read.HoldsNever<A> ignored -> false;
            case AffineConstraint.Read.Stated<A> stated -> proven(stated.constraint(), withRules);
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
    private Goal<A> below(CanonicalForm<A> form, Rational at) {
        return new Goal<>(form.coefs(), at.negated());
    }

    /**
     * Whether the rules prove {@code ¬(f rel 0)} — the invariant is <em>definitely</em> violated on
     * this path, which is a compile error rather than an undischarged obligation.
     *
     * <p>Which is proving the opposite comparison, and the opposite of each is one fact written
     * once. It had been a second switch over the relations, and a third reading of what they mean.
     */
    public boolean refutes(LinearForm<A> f, Rel rel) {
        return !isBottom() && entails(f, opposite(rel), true);
    }

    /** The comparison that holds exactly where {@code rel} does not. */
    private static Rel opposite(Rel rel) {
        return switch (rel) {
            case LE -> Rel.GT;
            case LT -> Rel.GE;
            case GE -> Rel.LT;
            case GT -> Rel.LE;
            case EQ -> Rel.NE;
            case NE -> Rel.EQ;
        };
    }

    /** A written form's weights, as the exact arithmetic holds them, with the positions it does not
     *  actually weigh left out. */
    private Map<A, Rational> weighed(LinearForm<A> f) {
        Map<A, Rational> coefs = new LinkedHashMap<>();
        f.coefs().forEach((atom, coef) -> {
            Rational weight = Rational.of(coef);
            if (!weight.isZero()) {
                coefs.put(atom, weight);
            }
        });
        return coefs;
    }

    /** A goal as a weighted sum and a constant, which is what a comparison against nought is. */
    private record Goal<A>(Map<A, Rational> coefs, Rational constant) {

        Goal<A> negated() {
            Map<A, Rational> out = new LinkedHashMap<>();
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
    private record Asked<A>(Goal<A> goal, Rational by) {}

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
        Map<A, Rational> coefs = weighed(f);
        Rational constant = Rational.of(f.constant());
        // Canonicalised by the one thing that canonicalises, so a question and a rule that say the
        // same thing are put into the same words by the same code. Doing the division here instead
        // would be a second account of what one rule is — which is the thing being removed.
        CanonicalForm.Scaled<A> scaled = CanonicalForm.of(coefs);
        if (scaled == null) {
            return new Asked<>(new Goal<>(Map.of(), constant), Rational.ONE);
        }
        return new Asked<>(
                new Goal<>(scaled.form().coefs(), constant.dividedBy(scaled.by())), scaled.by());
    }

    /**
     * Whether {@code Σ c·x + k <= 0} (or {@code < 0}) follows.
     *
     * <p>Two ways, and the second reads the first. What the box leaves the goal's own positions
     * bounds it; and a rule kept as written carries a goal onward wherever the box proves the
     * difference between the two — {@code f <= 0} together with {@code g - f <= 0} gives
     * {@code g <= 0}. That is what relates a guard over a computed value to what the type of the
     * value it was compared against guarantees.
     *
     * <p>One rule, once. The residual is proven against the box alone, so two rules are never added
     * together through this. What the box already holds of them is another matter and is not this
     * step: the rules that narrow it have all been read into it, each on its own.
     */
    private boolean proves(Goal<A> goal, boolean strict, boolean withRules) {
        RationalCut highest = highestProven(goal, withRules);
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
     * and the two readings had come apart in exactly the way the ranges and the proof once had
     *. So the routes, and the rule that a reading composes at most one other rule, are said
     * there and read from here.
     *
     * @param withRules false to ask what the ends and the closed relations between them say, leaving
     *                  the rules beside them out. A different question from what the rules say, and
     *                  the one an account of what was derived wants — and not the product of the
     *                  ranges either, which holds less than this does
     */
    private RationalCut highestProven(Goal<A> goal, boolean withRules) {
        FormReach<A> reading = reading();
        return withRules
                ? reading.most(goal.coefs(), goal.constant())
                : reading.mostFromTheEndsAndTheDifferences(goal.coefs(), goal.constant());
    }

    /** The one reading of what the rules leave a form, over the state they have been worked out to. */
    private FormReach<A> reading() {
        ClosedState<A> state = closed();
        return FormReach.over(rules, state.box(), state.differences());
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
     */
    public Bounds boundsOf(A atom) {
        if (isBottom()) {
            return new Bounds(null, null);
        }
        Box<A> box = closed().box();
        return new Bounds(written(box.leastOf(atom), false), written(box.mostOf(atom), true));
    }

    /**
     * The tightest bounds the rules prove on a whole form.
     *
     * <p>Read for a value the rules cannot carry directly: a product of two positions and a
     * truncating quotient are outside what this reasons in, and what they answer is bounded by what
     * their parts are proven to lie between.
     */
    public Bounds boundsOf(LinearForm<A> f) {
        if (isBottom()) {
            return new Bounds(null, null);
        }
        Asked<A> asked = goalOf(f);
        RationalCut highest = highestProven(asked.goal(), true);
        RationalCut lowest = highestProven(asked.goal().negated(), true);
        // Back into the units the caller asked in. The question was answered about the form divided
        // through by what its weights share, and the caller wants the form it wrote.
        return new Bounds(
                lowest == null ? null : written(new RationalCut(
                        lowest.at().negated().times(asked.by()), lowest.inclusive()), false),
                highest == null ? null : written(new RationalCut(
                        highest.at().times(asked.by()), highest.inclusive()), true));
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
    private Endpoint written(RationalCut cut, boolean upper) {
        if (cut == null) {
            return null;
        }
        BigDecimal exactly = cut.at().asWrittenDecimal();
        if (exactly != null) {
            return new Endpoint(new Count(exactly), cut.inclusive());
        }
        BigDecimal outward = cut.at().asDecimal(
                upper ? RoundingMode.CEILING : RoundingMode.FLOOR,
                DIGITS_WHEN_IT_IS_NOT_A_DECIMAL);
        // Rounded outward, the number itself is past where the rules stop, so it is admitted.
        return new Endpoint(new Count(outward), true);
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
        return kinds.keySet();
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

    /** What an atom's values are known to lie between. A {@code null} end is unbounded there. */
    public record Bounds(Endpoint min, Endpoint max) {

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

        /** The values this and {@code other} both hold. Each end is the tighter of the two, which
         * for a lower bound is the higher and for an upper bound the lower. */
        public Bounds meet(Bounds other) {
            return new Bounds(Endpoint.lower(min, other.min), Endpoint.upper(max, other.max));
        }

        /** Whether {@code at} is inside both ends — asked of the ends, because whether an end is one
         * of the counts it stops at is what the number alone does not say. */
        public boolean admits(Place at) {
            return (min == null || Endpoint.someValueLiesBetween(min, Endpoint.inclusive(at)))
                    && (max == null || Endpoint.someValueLiesBetween(Endpoint.inclusive(at), max));
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

    private static boolean writtenExactly(RationalCut cut) {
        return cut == null || cut.at().asWrittenDecimal() != null;
    }
}
