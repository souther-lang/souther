package souther.compiler.values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A reading of one value's positions, said in full before any of it is worked out.
 *
 * <p>What {@link AdmissibleValues} is, one step earlier. A position holds a description of the
 * values it admits ({@link AdmittedPlan}) rather than the values, and a choice this cannot tell the
 * branches of holds both. Turned into a reading by {@link #resolve}, which builds what has to be
 * built, once, under an allowance.
 *
 * <p><b>Why there are two types.</b> Whether the values are worked out decides which questions may
 * be asked: what a position admits, whether the reading speaks for it, whether anything stands
 * anywhere. Asked of this, every one of them would either be a guess or a machine built at the
 * moment somebody happened to ask — which is how what a clause costs came to depend on where its
 * brackets fell. So this holds only what the fold needs, and the answers live on the other side of
 * {@link #resolve}. There is no way back.
 *
 * @param <A> what a position is called
 */
public sealed interface PlannedValues<A> {

    /**
     * A reading whose shape is settled: these alternatives, or nothing at all.
     *
     * <p>The same nine things {@link AdmissibleValues} holds, with descriptions where it has sets.
     * What each of them is for is written there and is not written twice; what is different is that
     * a box may describe a set that turns out to be empty, since telling that is the work this
     * whole arrangement puts off.
     */
    record Settled<A>(PlannedHeld<A> held, Map<A, AdmittedPlan> perPosition,
                      Map<A, List<UnreadReason>> standing, boolean dropped,
                      Map<A, AdmittedPlan> guaranteed, AdmittedPlan defaultGuaranteed,
                      boolean guaranteedTogether, Set<A> tangled,
                      Set<A> widened) implements PlannedValues<A> {

        public Settled {
            perPosition = said(perPosition);
            standing = heldReasons(standing);
            // A guarantee empty at one position is empty at all of them — see
            // {@link AdmissibleValues}. Only what is settled empty counts: a description nobody has
            // worked out is not a reason to throw a promise away, and where it does turn out empty
            // the resolved reading drops it then.
            if (held instanceof PlannedHeld.Nothing
                    || defaultGuaranteed instanceof AdmittedPlan.Nothing
                    || guaranteed.values().stream().anyMatch(AdmittedPlan.Nothing.class::isInstance)) {
                guaranteed = Map.of();
                defaultGuaranteed = AdmittedPlan.NONE;
                guaranteedTogether = true;
            }
            guaranteed = Collections.unmodifiableMap(new LinkedHashMap<>(guaranteed));
            tangled = Collections.unmodifiableSet(new LinkedHashSet<>(tangled));
            widened = Collections.unmodifiableSet(new LinkedHashSet<>(widened));
        }
    }

    /**
     * A choice whose branches this cannot tell apart yet.
     *
     * <p>An interpreted connective and not an unread one: the clause said {@code ||} and this is
     * what {@code ||} means, held open only because which branch survives turns on values nobody
     * has worked out. What is done with it once they are is {@link AdmissibleValues#join}'s rules,
     * applied once and where they always were.
     *
     * <p>Made only where the question is open. A branch settled to admit nothing is answered here
     * and now, because nothing about that answer can change.
     *
     * @param apart whether the alternatives are to be held apart rather than merged, which the
     *              declaration settled before any of it was read
     */
    record Choice<A>(PlannedValues<A> left, PlannedValues<A> right,
                     boolean apart) implements PlannedValues<A> {

        public Choice {
            if (left == null || right == null) {
                throw new IllegalArgumentException("a choice is between two readings");
            }
        }
    }

    /** Nothing read and nothing missed, which is what a reading starts from. */
    static <A> PlannedValues<A> top() {
        return new Settled<>(PlannedHeld.one(new PlannedHeld.Box<>(Map.of())), Map.of(), Map.of(),
                false, Map.of(), AdmittedPlan.ANY, true, Set.of(), Set.of());
    }

    /** One position said to admit what {@code plan} describes, and nothing missed. */
    static <A> PlannedValues<A> at(A atom, AdmittedPlan plan) {
        Map<A, AdmittedPlan> said = Map.of(atom, plan);
        return new Settled<>(
                plan instanceof AdmittedPlan.Nothing ? new PlannedHeld.Nothing<>()
                        : PlannedHeld.one(new PlannedHeld.Box<>(said)),
                said, Map.of(), false, Map.of(atom, plan), AdmittedPlan.ANY, true, Set.of(),
                Set.of());
    }

    /**
     * A rule this could not read, which says nothing about any position and spoils the ones it
     * names — see {@link AdmissibleValues#unreadable}.
     */
    static <A> PlannedValues<A> unreadable(Set<A> named, UnreadReason why) {
        Map<A, List<UnreadReason>> spoiled = new LinkedHashMap<>();
        named.forEach(each -> spoiled.put(each, List.of(why)));
        return new Settled<>(PlannedHeld.one(new PlannedHeld.Box<>(Map.of())), Map.of(), spoiled,
                true, Map.of(), AdmittedPlan.NONE, true, Set.of(), Set.of());
    }

    /**
     * Whether anything is admitted, as far as the descriptions say so on their own.
     *
     * <p>Free, and no allowance is touched. {@link Emptiness#UNDECIDED} wherever telling would take
     * building something — which is most of the time, and is the point: a decision made here is a
     * decision made on what the walk had reached.
     */
    default Emptiness emptiness() {
        return switch (this) {
            case Choice<A> it -> it.left().emptiness().joined(it.right().emptiness());
            case Settled<A> it -> switch (it.held()) {
                case PlannedHeld.Nothing<A> _ -> Emptiness.EMPTY;
                // An alternative every position of which is settled to admit something is one
                // something stands in. Anywhere else the answer waits.
                case PlannedHeld.Alternatives<A> boxes -> boxes.boxes().stream()
                        .anyMatch(box -> box.at().values().stream()
                                .allMatch(plan -> plan instanceof AdmittedPlan.Of
                                        || plan instanceof AdmittedPlan.Everything))
                        ? Emptiness.NONEMPTY : Emptiness.UNDECIDED;
            };
        };
    }

    /** Whether nothing satisfies these rules, so far as that is settled. */
    default boolean isBottom() {
        return emptiness() == Emptiness.EMPTY;
    }

    /**
     * This where it already admits nothing, and a reading admitting nothing where it does not —
     * see {@link AdmissibleValues#leavingNothing}.
     */
    default PlannedValues<A> leavingNothing() {
        if (isBottom()) {
            return this;
        }
        return switch (this) {
            // Every branch of it, since what a caller showed impossible is the whole reading.
            case Choice<A> it -> new Choice<>(it.left().leavingNothing(),
                    it.right().leavingNothing(), it.apart());
            case Settled<A> it -> new Settled<>(new PlannedHeld.Nothing<>(), Map.of(),
                    it.standing(), it.dropped(), Map.of(), AdmittedPlan.NONE, true, it.tangled(),
                    it.widened());
        };
    }

    /**
     * Both readings holding at once.
     *
     * <p>Nothing is built and nothing can be refused: what two descriptions come to is a
     * description, so a conjunction costs what it costs to say and the saying is free.
     *
     * <p><b>Distributed over a choice this could not settle.</b> A conjunction of a choice is the
     * choice between the conjunctions, which is what a settled reading does to the alternatives it
     * holds — so an open choice keeps its branches and each of them meets what was stated beside it.
     * Merged into one first, the reading would be answering about a branch that may not be there.
     */
    default PlannedValues<A> meet(PlannedValues<A> other) {
        if (this instanceof Choice<A> it) {
            return new Choice<>(it.left().meet(other), it.right().meet(other), it.apart());
        }
        if (other instanceof Choice<A> it) {
            return new Choice<>(meet(it.left()), meet(it.right()), it.apart());
        }
        Settled<A> here = (Settled<A>) this;
        Settled<A> there = (Settled<A>) other;
        // Promising what both sides promise, where both promise their positions together — see
        // {@link AdmissibleValues#meet}, whose reasoning this is and which is not repeated.
        boolean apart = !here.guaranteedTogether() || !there.guaranteedTogether();
        return new Settled<>(met(here, there),
                narrowed(here.perPosition(), there.perPosition()),
                union(here.standing(), there.standing()), here.dropped() || there.dropped(),
                apart ? Map.of() : guaranteedBy(here, there, true),
                apart ? AdmittedPlan.NONE
                        : AdmittedPlan.meeting(List.of(here.defaultGuaranteed(),
                                there.defaultGuaranteed())),
                true,
                both(here.tangled(), there.tangled()),
                both(both(here.widened(), there.widened()),
                        both(here.tangled(), there.tangled())));
    }

    /**
     * The alternatives of a conjunction: every pair of one from each side.
     *
     * <p>Distributed rather than merged first, for the reason {@link AdmissibleValues} gives. What
     * is not done here is dropping the pairs nothing stands in: whether a pair stands is a question
     * about descriptions, and it is answered where they are worked out.
     */
    private static <A> PlannedHeld<A> met(Settled<A> here, Settled<A> there) {
        if (here.held() instanceof PlannedHeld.Nothing
                || there.held() instanceof PlannedHeld.Nothing) {
            return new PlannedHeld.Nothing<>();
        }
        Set<PlannedHeld.Box<A>> live = new LinkedHashSet<>();
        for (PlannedHeld.Box<A> one : alternatives(here)) {
            for (PlannedHeld.Box<A> two : alternatives(there)) {
                live.add(new PlannedHeld.Box<>(narrowed(one.at(), two.at())));
            }
        }
        return live.isEmpty() ? new PlannedHeld.Nothing<>()
                : new PlannedHeld.Alternatives<>(live);
    }

    private static <A> Set<PlannedHeld.Box<A>> alternatives(Settled<A> of) {
        return of.held() instanceof PlannedHeld.Alternatives<A> it ? it.boxes() : Set.of();
    }

    /** Both sides holding at each position, each side missing one holding every value. */
    private static <A> Map<A, AdmittedPlan> narrowed(Map<A, AdmittedPlan> these,
                                                     Map<A, AdmittedPlan> those) {
        Map<A, AdmittedPlan> out = new LinkedHashMap<>(these);
        those.forEach((atom, plan) ->
                out.merge(atom, plan, (one, other) -> AdmittedPlan.meeting(List.of(one, other))));
        return out;
    }

    /** What both sides guarantee, at every position either holds a guarantee for, each side
     *  missing one standing at its own default. */
    private static <A> Map<A, AdmittedPlan> guaranteedBy(Settled<A> here, Settled<A> there,
                                                         boolean met) {
        Set<A> named = new LinkedHashSet<>(here.guaranteed().keySet());
        named.addAll(there.guaranteed().keySet());
        Map<A, AdmittedPlan> out = new LinkedHashMap<>();
        named.forEach(each -> {
            List<AdmittedPlan> two = List.of(
                    here.guaranteed().getOrDefault(each, here.defaultGuaranteed()),
                    there.guaranteed().getOrDefault(each, there.defaultGuaranteed()));
            out.put(each, met ? AdmittedPlan.meeting(two) : AdmittedPlan.joining(two));
        });
        return out;
    }

    /** What each position holds across the alternatives, which a description makes free. */
    default AdmittedPlan at(A atom) {
        return switch (this) {
            case Choice<A> it -> AdmittedPlan.joining(
                    List.of(it.left().at(atom), it.right().at(atom)));
            case Settled<A> it -> across(it, atom);
        };
    }

    /** What one position holds across a settled reading's alternatives. */
    private static <A> AdmittedPlan across(Settled<A> of, A atom) {
        return switch (of.held()) {
            case PlannedHeld.Nothing<A> _ -> of.perPosition().getOrDefault(atom, AdmittedPlan.ANY);
            case PlannedHeld.Alternatives<A> boxes -> AdmittedPlan.joining(
                    boxes.boxes().stream().map(box -> box.get(atom)).toList());
        };
    }

    /**
     * Either reading holding, the alternatives merged into one product.
     *
     * <p>What a choice leaves depends on which of its branches can be taken, and that is a question
     * about values. Where the descriptions settle it, it is settled here and the rules are the ones
     * a finished reading uses. Where they do not, the choice is kept open ({@link Choice}) and the
     * same rules are applied once, later, to the same two branches — so what a choice comes to is
     * the same whichever of those happened, and neither depends on how much of the clause had been
     * read when the question came up.
     */
    default PlannedValues<A> join(PlannedValues<A> other) {
        return joining(other, false);
    }

    /** Either reading holding, with the alternatives of the two held apart — see
     *  {@link AdmissibleValues#joinApart}. */
    default PlannedValues<A> joinApart(PlannedValues<A> other) {
        return joining(other, true);
    }

    private PlannedValues<A> joining(PlannedValues<A> other, boolean apart) {
        Emptiness here = emptiness();
        Emptiness there = other.emptiness();
        // An alternative nobody can take leaves the answer to the other, and both being that is a
        // reading admitting nothing. Settled now because nothing about it can change: a branch that
        // admits nothing admits nothing whatever is written beside it.
        if (here == Emptiness.EMPTY && there == Emptiness.EMPTY) {
            return bothDead(other);
        }
        if (here == Emptiness.EMPTY) {
            return besideDead(other, this);
        }
        if (there == Emptiness.EMPTY) {
            return besideDead(this, other);
        }
        // And where neither is settled, the question waits. Both branches are kept whole, since
        // which of them survives decides what the other one owes.
        return new Choice<>(this, other, apart);
    }

    /**
     * A choice one branch of which nobody can take, which is the other branch.
     *
     * <p>What the dead one said goes with it. Nothing satisfies it, so what it left a position is
     * not something a value of this type is under — its unread rules included, which is why the
     * reasons do not travel either. What it does leave is the account of adoption, and that is the
     * clause reading's to keep ({@code StatedByClauses}).
     */
    private static <A> PlannedValues<A> besideDead(PlannedValues<A> live, PlannedValues<A> dead) {
        return live;
    }

    /**
     * A choice neither branch of which anybody can take.
     *
     * <p>No branch speaks for the other, so answering with either would settle the proof by the
     * order the operands were written in. What is left is the positions both of them leave nothing
     * at, which is an answer about the whole value — see {@link AdmissibleValues#joinApart}, whose
     * reasoning this is.
     */
    private PlannedValues<A> bothDead(PlannedValues<A> other) {
        Settled<A> here = settled();
        Settled<A> there = other.settled();
        Map<A, AdmittedPlan> empty = new LinkedHashMap<>();
        adopted(here).forEach(atom -> {
            if (at(atom) instanceof AdmittedPlan.Nothing
                    && other.at(atom) instanceof AdmittedPlan.Nothing) {
                empty.put(atom, AdmittedPlan.NONE);
            }
        });
        return new Settled<>(new PlannedHeld.Nothing<>(), empty,
                union(here.standing(), there.standing()), here.dropped() || there.dropped(),
                Map.of(), AdmittedPlan.NONE, true,
                both(here.tangled(), there.tangled()), both(here.widened(), there.widened()));
    }

    /**
     * A choice both branches of which stand, as one description.
     *
     * <p>The rules are {@link AdmissibleValues#joinApart}'s and the reasoning is written there.
     * What is here is the same arithmetic over descriptions rather than sets, which is why it costs
     * nothing and can be done before anything is built.
     */
    private PlannedValues<A> joinedLive(PlannedValues<A> other, boolean apart) {
        Settled<A> here = settled();
        Settled<A> there = other.settled();
        Map<A, AdmittedPlan> covered = guaranteedBy(here, there, false);
        AdmittedPlan coveredElsewhere = AdmittedPlan.joining(
                List.of(here.defaultGuaranteed(), there.defaultGuaranteed()));
        Map<A, List<UnreadReason>> spoiled = union(here.standing(), there.standing());
        if (there.dropped()) {
            spoiled = spoiling(spoiled, promisedAt(here));
        }
        if (here.dropped()) {
            spoiled = spoiling(spoiled, promisedAt(there));
        }
        Set<A> shapedBy = new LinkedHashSet<>(promisedAt(here));
        shapedBy.addAll(promisedAt(there));
        return new Settled<>(apart ? apart(here, there) : merged(here, there),
                widenedBy(here.perPosition(), there.perPosition()), spoiled,
                here.dropped() || there.dropped(), covered, coveredElsewhere,
                here.guaranteedTogether() && there.guaranteedTogether() && shapedBy.size() <= 1,
                apart || shapedBy.size() <= 1 ? both(here.tangled(), there.tangled())
                        : both(both(here.tangled(), there.tangled()), shapedBy),
                both(here.widened(), there.widened()));
    }

    /** The alternatives of both, which is what the choice leaves where they are held apart. */
    private static <A> PlannedHeld<A> apart(Settled<A> here, Settled<A> there) {
        Set<PlannedHeld.Box<A>> boxes = new LinkedHashSet<>(alternatives(here));
        boxes.addAll(alternatives(there));
        return new PlannedHeld.Alternatives<>(boxes);
    }

    /** The one product holding both readings' alternatives, which is what a choice comes to while
     *  the alternatives are held one at a time. */
    private static <A> PlannedHeld<A> merged(Settled<A> here, Settled<A> there) {
        Map<A, AdmittedPlan> out = new LinkedHashMap<>();
        adopted(here).forEach(atom -> {
            AdmittedPlan theirs = across(there, atom);
            // A position one side says nothing about is one the choice says nothing about, since a
            // value satisfying that side may hold anything there.
            if (!(theirs instanceof AdmittedPlan.Everything)) {
                out.put(atom, AdmittedPlan.joining(List.of(across(here, atom), theirs)));
            }
        });
        return PlannedHeld.one(new PlannedHeld.Box<>(out));
    }

    /** Either side holding at each position, which is what both spoke about. */
    private static <A> Map<A, AdmittedPlan> widenedBy(Map<A, AdmittedPlan> these,
                                                      Map<A, AdmittedPlan> those) {
        Map<A, AdmittedPlan> out = new LinkedHashMap<>();
        these.forEach((atom, plan) -> {
            AdmittedPlan there = those.get(atom);
            if (there != null) {
                out.put(atom, AdmittedPlan.joining(List.of(plan, there)));
            }
        });
        return out;
    }

    /** The positions an alternative beside this one may have widened — see
     *  {@link AdmissibleValues}. */
    private static <A> Set<A> promisedAt(Settled<A> of) {
        return of.guaranteed().keySet();
    }

    /** The same reasons, and one more at each position an unread alternative stood beside. */
    private static <A> Map<A, List<UnreadReason>> spoiling(Map<A, List<UnreadReason>> standing,
                                                           Set<A> named) {
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(standing);
        named.forEach(each -> out.putIfAbsent(each, List.of(UnreadReason.ALTERNATIVE_NOT_READ)));
        return out;
    }

    /**
     * This as a settled reading, which a branch admitting nothing always is.
     *
     * <p>A choice is kept open only where neither branch is settled empty, so anything that reached
     * here by being empty is one. Written as a cast rather than as an arm, because the alternative
     * is an arm nothing can reach and a reader wondering what it would mean.
     */
    private Settled<A> settled() {
        if (this instanceof Settled<A> it) {
            return it;
        }
        throw new IllegalStateException("a choice nobody could settle is not a settled reading");
    }

    /** The positions this holds an answer about, in the order they were read. */
    private static <A> Set<A> adopted(Settled<A> of) {
        Set<A> out = new LinkedHashSet<>();
        switch (of.held()) {
            case PlannedHeld.Nothing<A> _ -> out.addAll(of.perPosition().keySet());
            case PlannedHeld.Alternatives<A> it ->
                    it.boxes().forEach(box -> out.addAll(box.at().keySet()));
        }
        return out;
    }

    /**
     * The reading this describes, with everything it describes worked out.
     *
     * <p>The one way across, and there is no way back. What is built is built here, once, under
     * {@code by}'s allowance; a choice this could not settle is settled from the values, by the
     * rules a finished reading has always used; and where the allowance ran out, the position is
     * left holding every value with {@link UnreadReason#EXACT_VALUES_TOO_COSTLY} standing at it.
     *
     * <p>So a reading that has arrived has no decision left in it. Nothing downstream builds a
     * machine, and nothing downstream is holding a description of an answer as though it were one.
     */
    default AdmissibleValues<A> resolve(Realizer by) {
        return switch (this) {
            case Choice<A> it -> {
                // What the question was waiting for: whether either branch admits anything. Asked
                // of the branches worked out, and of nothing else.
                AdmissibleValues<A> left = it.left().resolve(by);
                AdmissibleValues<A> right = it.right().resolve(by);
                if (left.isBottom() && right.isBottom()) {
                    yield it.left().bothDead(it.right()).resolve(by);
                }
                if (left.isBottom()) {
                    yield right;
                }
                if (right.isBottom()) {
                    yield left;
                }
                // And where both stand, the choice is put together as a description and built once.
                // Joined as the two readings above instead, every position of it would be a machine
                // made out of sets that were already machines, which is work nobody described.
                yield it.left().joinedLive(it.right(), it.apart()).resolve(by);
            }
            case Settled<A> it -> resolved(it, by);
        };
    }

    private static <A> AdmissibleValues<A> resolved(Settled<A> of, Realizer by) {
        Set<A> gaveUp = new LinkedHashSet<>();
        Map<A, ValueSet> perPosition = realized(of.perPosition(), by, gaveUp);
        Map<A, ValueSet> guaranteed = promised(of.guaranteed(), by);
        AdmissibleValues.Held<A> held = switch (of.held()) {
            case PlannedHeld.Nothing<A> _ -> new AdmissibleValues.Held.Nothing<A>();
            case PlannedHeld.Alternatives<A> boxes -> alternatives(boxes, by, gaveUp);
        };
        return new AdmissibleValues<>(held, perPosition,
                alsoStanding(of.standing(), gaveUp), of.dropped(),
                guaranteed, promise(of.defaultGuaranteed(), by), of.guaranteedTogether(),
                of.tangled(), PlannedValues.both(of.widened(), gaveUp));
    }

    /**
     * The alternatives, with the ones nothing stands in dropped.
     *
     * <p>Where the invariant a settled reading has is kept: a box with a side admitting nothing
     * stands for nothing, and now that the sides are values it can be seen and taken out. Where
     * every box goes, nothing satisfies the rules.
     */
    private static <A> AdmissibleValues.Held<A> alternatives(PlannedHeld.Alternatives<A> boxes,
                                                             Realizer by, Set<A> gaveUp) {
        Set<AdmissibleValues.Box<A>> live = new LinkedHashSet<>();
        Set<PlannedHeld.Box<A>> standing = new LinkedHashSet<>();
        for (PlannedHeld.Box<A> box : boxes.boxes()) {
            Map<A, ValueSet> at = realized(box.at(), by, gaveUp);
            if (at.values().stream().noneMatch(ValueSet::isEmpty)) {
                live.add(new AdmissibleValues.Box<>(at));
                standing.add(box);
            }
        }
        if (live.isEmpty()) {
            return new AdmissibleValues.Held.Nothing<>();
        }
        // What each position holds across the ones that stand, described first and built once. Read
        // off the sets instead, a join of two languages would be a machine nobody counted.
        Set<A> named = new LinkedHashSet<>();
        standing.forEach(box -> named.addAll(box.at().keySet()));
        Map<A, ValueSet> across = new LinkedHashMap<>();
        for (A atom : named) {
            AdmittedPlan plan = AdmittedPlan.joining(
                    standing.stream().map(box -> box.get(atom)).toList());
            Realization made = by.of(plan);
            if (!made.isExact()) {
                gaveUp.add(atom);
            }
            if (!made.upperBound().isAny()) {
                across.put(atom, made.upperBound());
            }
        }
        return AdmissibleValues.Held.Alternatives.of(live, across);
    }

    /** Each position's description as the set it comes to, the ones nobody could build widened to
     *  every value and written down as such. */
    private static <A> Map<A, ValueSet> realized(Map<A, AdmittedPlan> of, Realizer by,
                                                 Set<A> gaveUp) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        of.forEach((atom, plan) -> {
            Realization made = by.of(plan);
            if (!made.isExact()) {
                gaveUp.add(atom);
            }
            out.put(atom, made.upperBound());
        });
        return out;
    }

    /**
     * The same for a promise, which widens the other way.
     *
     * <p>A promise nobody could work out promises nothing, and that is the strongest thing that
     * stays true — where an answer this could not build widens to every value, a guarantee it could
     * not build shrinks to none. Nothing is recorded: a reader short of a guarantee has been told
     * no more than the truth, and the reasons below are about the upper bound.
     */
    private static <A> Map<A, ValueSet> promised(Map<A, AdmittedPlan> of, Realizer by) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        of.forEach((atom, plan) -> out.put(atom, promise(plan, by)));
        return out;
    }

    private static ValueSet promise(AdmittedPlan plan, Realizer by) {
        Realization made = by.of(plan);
        return made.isExact() ? made.upperBound() : ValueSet.NONE;
    }

    /** The reasons, and one more at each position whose answer was not built — see
     *  {@link AdmissibleValues}. */
    private static <A> Map<A, List<UnreadReason>> alsoStanding(Map<A, List<UnreadReason>> standing,
                                                               Set<A> gaveUp) {
        if (gaveUp.isEmpty()) {
            return standing;
        }
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(standing);
        gaveUp.forEach(atom -> {
            List<UnreadReason> why = new ArrayList<>(out.getOrDefault(atom, List.of()));
            why.add(UnreadReason.EXACT_VALUES_TOO_COSTLY);
            out.put(atom, why);
        });
        return out;
    }

    /** Every subject this reading is filed under — see {@link AdmissibleValues#subjects}. */
    default Set<A> subjects() {
        Set<A> out = new LinkedHashSet<>();
        switch (this) {
            case Choice<A> it -> {
                out.addAll(it.left().subjects());
                out.addAll(it.right().subjects());
            }
            case Settled<A> it -> {
                if (it.held() instanceof PlannedHeld.Alternatives<A> boxes) {
                    boxes.boxes().forEach(box -> out.addAll(box.at().keySet()));
                }
                out.addAll(it.perPosition().keySet());
                out.addAll(it.standing().keySet());
                out.addAll(it.guaranteed().keySet());
                out.addAll(it.tangled());
                out.addAll(it.widened());
            }
        }
        return Collections.unmodifiableSet(out);
    }

    /** The same reading under other names — see {@link AdmissibleValues#renamed}. */
    default <B> PlannedValues<B> renamed(java.util.function.Function<A, B> naming) {
        return switch (this) {
            case Choice<A> it -> new Choice<>(it.left().renamed(naming),
                    it.right().renamed(naming), it.apart());
            case Settled<A> it -> new Settled<>(renamedHeld(it.held(), naming),
                    renamedKeys(it.perPosition(), naming), renamedKeys(it.standing(), naming),
                    it.dropped(), renamedKeys(it.guaranteed(), naming), it.defaultGuaranteed(),
                    it.guaranteedTogether(), renamedNames(it.tangled(), naming),
                    renamedNames(it.widened(), naming));
        };
    }

    private static <A, B> PlannedHeld<B> renamedHeld(PlannedHeld<A> held,
                                                     java.util.function.Function<A, B> naming) {
        return switch (held) {
            case PlannedHeld.Nothing<A> _ -> new PlannedHeld.Nothing<B>();
            case PlannedHeld.Alternatives<A> it -> {
                Set<PlannedHeld.Box<B>> boxes = new LinkedHashSet<>();
                it.boxes().forEach(box -> boxes.add(
                        new PlannedHeld.Box<>(renamedKeys(box.at(), naming))));
                yield new PlannedHeld.Alternatives<>(boxes);
            }
        };
    }

    private static <A, B, V> Map<B, V> renamedKeys(Map<A, V> of,
                                                   java.util.function.Function<A, B> naming) {
        Map<B, V> out = new LinkedHashMap<>();
        of.forEach((position, value) -> out.put(naming.apply(position), value));
        return out;
    }

    private static <A, B> Set<B> renamedNames(Set<A> of, java.util.function.Function<A, B> naming) {
        Set<B> out = new LinkedHashSet<>();
        of.forEach(position -> out.add(naming.apply(position)));
        return out;
    }

    /** What was said, which is what is not every value: a position nothing narrowed is held by
     *  being absent, and holding it would make one reading two states. */
    private static <A> Map<A, AdmittedPlan> said(Map<A, AdmittedPlan> at) {
        Map<A, AdmittedPlan> out = new LinkedHashMap<>();
        at.forEach((atom, plan) -> {
            if (!(plan instanceof AdmittedPlan.Everything)) {
                out.put(atom, plan);
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /** The reasons kept as they were given — see {@link AdmissibleValues}. */
    private static <A> Map<A, List<UnreadReason>> heldReasons(Map<A, List<UnreadReason>> why) {
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>();
        why.forEach((atom, reasons) -> {
            if (!reasons.isEmpty()) {
                out.put(atom, List.copyOf(reasons));
            }
        });
        return Collections.unmodifiableMap(out);
    }

    /** Every position of either, in the order they were recorded. */
    static <A> Set<A> both(Set<A> these, Set<A> those) {
        if (those.isEmpty()) {
            return these;
        }
        if (these.isEmpty()) {
            return those;
        }
        Set<A> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }

    /** Every reason of either, at every position either names, in the order they were met. */
    static <A> Map<A, List<UnreadReason>> union(Map<A, List<UnreadReason>> these,
                                                Map<A, List<UnreadReason>> those) {
        if (those.isEmpty()) {
            return these;
        }
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(these);
        those.forEach((atom, reasons) -> {
            List<UnreadReason> all = new ArrayList<>(out.getOrDefault(atom, List.of()));
            all.addAll(reasons);
            out.put(atom, all);
        });
        return out;
    }
}
