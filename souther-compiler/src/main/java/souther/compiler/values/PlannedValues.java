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
        return anyAlternativeAdmits((_, _) -> Emptiness.NONEMPTY);
    }

    /**
     * Whether an alternative survives a question asked of every position it names, out of the
     * descriptions alone.
     *
     * <p>{@link AdmissibleValues#anyAlternativeAdmits}'s walk over a reading that has not been
     * worked out, and the same rule: an alternative stands where every position of it still admits
     * something, and the reading stands where any alternative does.
     *
     * <p><b>The question is asked of a position only where answering it needs no machine.</b> A
     * description this has already got a set for is one the caller may be asked about; a pattern is
     * a machine somebody has to make, and making one here is the work this whole arrangement puts
     * off — so the position waits, and the alternative waits with it. What must not happen is
     * answering the caller's question from the description alone: a position whose plan is already
     * a set admits something and may still share none with what the caller knows, and a reading
     * that called that alternative live settled a branch nobody can be in as one somebody can.
     */
    default Emptiness anyAlternativeAdmits(AskedOfEachPosition<A> asked) {
        return switch (this) {
            case Settled<A> it -> switch (it.held()) {
                case PlannedHeld.Nothing<A> _ -> Emptiness.EMPTY;
                case PlannedHeld.Alternatives<A> boxes -> {
                    Emptiness any = Emptiness.EMPTY;
                    for (PlannedHeld.Box<A> box : boxes.boxes()) {
                        Emptiness stands = Emptiness.NONEMPTY;
                        for (Map.Entry<A, AdmittedPlan> each : box.at().entrySet()) {
                            stands = stands.met(askedOf(each.getKey(), each.getValue(), asked));
                            if (stands == Emptiness.EMPTY) {
                                break;
                            }
                        }
                        any = any.joined(stands);
                        if (any == Emptiness.NONEMPTY) {
                            yield any;
                        }
                    }
                    yield any;
                }
            };
        };
    }

    /** What one position's description comes to under the question, waiting where a machine would
     *  have to be made to ask it. */
    private static <A> Emptiness askedOf(A position, AdmittedPlan plan,
                                         AskedOfEachPosition<A> asked) {
        return switch (plan) {
            case AdmittedPlan.Nothing _ -> Emptiness.EMPTY;
            case AdmittedPlan.Everything _ -> asked.of(position, ValueSet.ANY);
            case AdmittedPlan.Of it -> asked.of(position, it.set());
            case AdmittedPlan.Pattern _, AdmittedPlan.Both _, AdmittedPlan.Either _ ->
                    Emptiness.UNDECIDED;
        };
    }

    /**
     * What a rule left standing at each position, and what stopped this reading taking it in.
     *
     * <p>Bookkeeping about the rules and not about the values, so it is here rather than on the
     * other side of {@link #resolve}: a caller answering for which rule stopped where is asking
     * about what was read, and that is known as soon as it is read. What resolve adds is the one
     * reason that is about the answer and not about a rule.
     */
    default Map<A, List<UnreadReason>> standing() {
        return switch (this) {
            case Settled<A> it -> it.standing();
        };
    }

    /** Whether a rule was left unread anywhere in this reading — see {@link AdmissibleValues}. */
    default boolean dropped() {
        return switch (this) {
            case Settled<A> it -> it.dropped();
        };
    }

    /**
     * Whether nothing is admitted, taking in what {@code by} has already worked out as well.
     *
     * <p>{@link #emptiness} answers off the descriptions alone, and a language is a description of
     * a machine rather than the set it comes to — so two patterns nothing satisfies together read
     * as undecided there, and stay undecided until something builds them. This asks the same
     * question of the position's answer, which may have built exactly that: what a branch of a rule
     * came to is a plan, and where the reading of the whole value already worked that plan out, the
     * result is there to be read.
     *
     * <p>Nothing is built and nothing is spent. So a false here is "nothing established that this
     * is empty" and never "something stands in this" — a caller acting on it declines to claim
     * rather than claiming the opposite.
     */
    default boolean holdsNothingAsBuilt(Allowance<A> by) {
        if (emptiness() == Emptiness.EMPTY) {
            return true;
        }
        for (A atom : subjects()) {
            ValueSet known = by.known(atom, at(atom));
            if (known != null && known.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /**
     * The positions this reading narrowed, which is what a reader asking what it took in is asking.
     *
     * <p>Free, and no allowance is touched: a position was narrowed where what it holds is not
     * every value, and a description says which of those it is by being one shape or another.
     */
    default Set<A> adoptedAt() {
        Set<A> out = new LinkedHashSet<>();
        adoptedIn(this).forEach(atom -> {
            if (!(at(atom) instanceof AdmittedPlan.Everything)) {
                out.add(atom);
            }
        });
        return out;
    }

    private static <A> Set<A> adoptedIn(PlannedValues<A> of) {
        return switch (of) {
            case Settled<A> it -> adopted(it);
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
     * <p>A choice whose branches are not settled is not one of these. Which branch of a clause
     * survives is a question about the whole of what was read of it — the values and the order
     * together — so it is held a layer out, where both of those are ({@code StatedByClauses}), and
     * a conjunction distributes over it there.
     */
    default PlannedValues<A> meet(PlannedValues<A> other) {
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
     * Either reading holding, both branches being ones somebody can take.
     *
     * <p>Which branches those are is not decided here. What a choice leaves turns on whether either
     * branch admits anything, and that is a question about the whole of what was read of the clause
     * — the values and the order together — so it is asked a layer out and this is called with the
     * answer already in hand ({@code StatedByClauses}). Asked here as well, the two would be two
     * answers to one question, and the one made of values alone would drop a branch the order
     * refused and keep one the values did.
     */
    default PlannedValues<A> join(PlannedValues<A> other) {
        return joinedLive(other, false);
    }

    /** Either reading holding, with the alternatives of the two held apart — see
     *  {@link AdmissibleValues#joinApart}. */
    default PlannedValues<A> joinApart(PlannedValues<A> other) {
        return joinedLive(other, true);
    }

    /**
     * A choice neither branch of which anybody can take.
     *
     * <p>No branch speaks for the other, so answering with either would settle the proof by the
     * order the operands were written in. What is left is the positions both of them leave nothing
     * at, which is an answer about the whole value — see {@link AdmissibleValues#joinApart}, whose
     * reasoning this is.
     */
    default PlannedValues<A> bothDead(PlannedValues<A> other) {
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
            spoiled = UnreadReason.leftOpen(spoiled, promisedAt(here));
        }
        if (here.dropped()) {
            spoiled = UnreadReason.leftOpen(spoiled, promisedAt(there));
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
     *
     * <p><b>And what could not be built comes back beside it.</b> Whether the reading admits
     * anything, and which limit stopped this compiler, are settled by the same work — and a caller
     * given the values alone has to guess them from a set widened to everything, where every guess
     * is the wrong one. See {@link Realized}.
     */
    default Realized<A> resolve(Allowance<A> by) {
        return switch (this) {
            case Settled<A> it -> resolved(it, by);
        };
    }

    /**
     * The machines this reading asks for.
     *
     * <p>What a refusal is answered from. A machine is made under a position's allowance, where
     * every rule reaching the position has paid in, so which reading asked for the one that was
     * refused is a question the far end cannot answer — and this is what a reading holds so that it
     * can be answered here instead of guessed from which positions somebody named.
     *
     * <p>The patterns and not the places they were written. A machine is the pattern's, so a
     * reading that asked for one is one that asked for that pattern, and two readings asking for
     * the same pattern are two answerable for one refusal — which is what writing the same clause
     * twice comes to and is not something to tell apart here.
     */
    default Set<Asked<A>> asked() {
        Settled<A> it = settled();
        Set<Asked<A>> out = new LinkedHashSet<>();
        it.perPosition().forEach((atom, plan) -> asked(out, atom, plan));
        switch (it.held()) {
            case PlannedHeld.Nothing<A> _ -> { }
            case PlannedHeld.Alternatives<A> boxes -> boxes.boxes().forEach(box ->
                    box.at().forEach((atom, plan) -> asked(out, atom, plan)));
        }
        return out;
    }

    private static <A> void asked(Set<Asked<A>> out, A atom, AdmittedPlan plan) {
        plan.asked().forEach(each -> out.add(new Asked<>(atom, each)));
    }

    /**
     * One machine a reading asked for, and the position it was asked for.
     *
     * <p>Both, because a refusal is about both. A machine is the pattern's, so the same pattern
     * written into two rules is one machine that both asked for; an allowance is the position's, so
     * a machine refused while one position was worked out is nothing another position's rules
     * asked. Keyed by the pattern alone, a rule that wrote that pattern about one position was
     * handed a refusal that happened at another — the same shape as answering from the place, one
     * axis over.
     *
     * @param at the position whose answer the machine was being built for
     * @param plan the pattern whose machine it is
     */
    record Asked<A>(A at, souther.compiler.regex.PatternPlan plan) {

        public Asked {
            if (at == null || plan == null) {
                throw new IllegalArgumentException(
                        "a machine is asked for by a pattern, for a position");
            }
        }
    }

    private static <A> Realized<A> resolved(Settled<A> of, Allowance<A> by) {
        Unbuilt<A> gaveUp = new Unbuilt<>();
        Map<A, ValueSet> perPosition = realized(of.perPosition(), by, gaveUp);
        Map<A, ValueSet> guaranteed = promised(of.guaranteed(), by);
        AdmissibleValues.Held<A> held = switch (of.held()) {
            case PlannedHeld.Nothing<A> _ -> new AdmissibleValues.Held.Nothing<A>();
            case PlannedHeld.Alternatives<A> boxes -> alternatives(boxes, by, gaveUp);
        };
        return new Realized<>(new AdmissibleValues<>(held, perPosition,
                gaveUp.beside(of.standing()), of.dropped(),
                guaranteed, promised(of.defaultGuaranteed(), by.elsewhere()),
                of.guaranteedTogether(),
                of.tangled(), PlannedValues.both(of.widened(), gaveUp.names())),
                gaveUp.aboutARule(), gaveUp.aboutTheAnswer());
    }

    /**
     * The same reading with more said about what stopped it.
     *
     * <p>For a caller that worked a branch out to decide something and has to keep what it learned.
     * A branch probed and not built is one this compiler could not show empty, and where it is kept
     * as a branch anybody might be in, the reason nobody knows has to be kept with it — dropped,
     * the reading says a position is open where what is true is that nothing looked.
     */
    default PlannedValues<A> alsoStanding(Map<A, List<UnreadReason>> why) {
        if (why.isEmpty()) {
            return this;
        }
        Settled<A> it = settled();
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(it.standing());
        why.forEach((atom, mine) -> {
            List<UnreadReason> all = new ArrayList<>(out.getOrDefault(atom, List.of()));
            mine.forEach(each -> {
                if (!all.contains(each)) {
                    all.add(each);
                }
            });
            out.put(atom, all);
        });
        return new Settled<>(it.held(), it.perPosition(), out, it.dropped(), it.guaranteed(),
                it.defaultGuaranteed(), it.guaranteedTogether(), it.tangled(),
                both(it.widened(), why.keySet()));
    }

    /**
     * The alternatives, with the ones nothing stands in dropped.
     *
     * <p>Where the invariant a settled reading has is kept: a box with a side admitting nothing
     * stands for nothing, and now that the sides are values it can be seen and taken out. Where
     * every box goes, nothing satisfies the rules.
     */
    private static <A> AdmissibleValues.Held<A> alternatives(PlannedHeld.Alternatives<A> boxes,
                                                             Allowance<A> by, Unbuilt<A> gaveUp) {
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
            Realization made = by.realizer(atom).of(plan);
            gaveUp.note(atom, made);
            if (!made.upperBound().isAny()) {
                across.put(atom, made.upperBound());
            }
        }
        return AdmissibleValues.Held.Alternatives.of(live, across);
    }

    /** Each position's description as the set it comes to, the ones nobody could build widened to
     *  every value and written down as such. */
    private static <A> Map<A, ValueSet> realized(Map<A, AdmittedPlan> of, Allowance<A> by,
                                                 Unbuilt<A> gaveUp) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        of.forEach((atom, plan) -> {
            Realization made = by.realizer(atom).of(plan);
            gaveUp.note(atom, made);
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
    private static <A> Map<A, ValueSet> promised(Map<A, AdmittedPlan> of, Allowance<A> by) {
        Map<A, ValueSet> out = new LinkedHashMap<>();
        of.forEach((atom, plan) -> out.put(atom, promised(plan, by.realizer(atom))));
        return out;
    }

    private static ValueSet promised(AdmittedPlan plan, Realizer by) {
        Realization made = by.of(plan);
        return made.isExact() ? made.upperBound() : ValueSet.NONE;
    }

    /** Every subject this reading is filed under — see {@link AdmissibleValues#subjects}. */
    default Set<A> subjects() {
        Set<A> out = new LinkedHashSet<>();
        switch (this) {
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
