package souther.compiler.partition;

import souther.compiler.carrier.Lookup;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What a row has already had to satisfy by the time it arrives at one comparison.
 *
 * <p>The region a border a guard owes is searched in. A guard states a threshold and narrows no
 * declaration, so what the positions are declared to hold is the same everywhere in a body while
 * what actually arrives at a comparison deep in one is not — and a row for a border down there,
 * looked for over the declared domains, is looked for outside the region as readily as inside it.
 *
 * <p><b>Collected where the condition is assumed, and never worked out afterwards from where a
 * comparison sits.</b> A reading that walked back up the tree would be a second account of what was
 * assumed, free to name a condition nothing here could take in — and a region narrowed on a
 * condition nothing established is narrower than the rows that arrive, which is the one direction
 * that takes a coverage item away. So what is here is what the walk itself put in.
 *
 * <p><b>Including what it could not put in.</b> A condition the arithmetic has no word for narrows
 * nothing, and it is written down all the same: what a region is is one question and how it came to
 * be that region is another, and only the second can tell a search that ran over what the
 * declarations leave because nothing stood in the way from one that ran over the same box because a
 * guard above could not be read. Held as {@link OnTheWay}, so the two are one sequence in the order
 * the walk met them rather than a list and a silence.
 *
 * <p><b>Its own value and not its arm.</b> Under {@code A && B} the {@code then} arm is reached with
 * both holding, and the {@code else} arm with neither settled — a row can be in it for failing
 * either. Under {@code A || B} it is the other way round. Which of the two a comparison is in is
 * {@link GuardThresholds}'s reading of the condition, and taking an arm for a conjunct is how a
 * region would come to exclude rows that reach the guard.
 *
 * <p>Nothing here says a row that satisfies all of this arrives. A condition of a shape the
 * arithmetic cannot read is on the list without narrowing anything, so a region built from this
 * holds every row that arrives and may hold rows that do not — which is what {@link SearchRegion}
 * promises and what a proof of unreachability rests on. It is the inclusion and not a strict one:
 * a condition nothing took in may be implied by the ones that were, or hold of every row. Being on
 * the list is what lets a report say a condition is unaccounted for; it is not what the region is
 * built from.
 */
public record ReachingCuts(Lookup<ALine, List<OnTheWay>> byLine,
                           Lookup<ModelOccurrence, ConditionOnTheWay> byTruth,
                           Lookup<ModelOccurrence, ConditionOnTheWay> byFork) {

    public static final ReachingCuts NONE = new ReachingCuts(Lookup.built(_ -> { }),
            Lookup.built(_ -> { }), Lookup.built(_ -> { }));

    public ReachingCuts {
        Objects.requireNonNull(byLine, "what a walk collected, line by line");
        Objects.requireNonNull(byTruth, "what a walk collected, truth by truth");
        Objects.requireNonNull(byFork, "what a walk collected, fork by fork");
    }

    /**
     * Which line of which comparison a row is looked for at.
     *
     * <p>The comparison, and which of its lines where it states several. Those are reached by one
     * way and looked for under more than it: a line of {@code Int.max(a, b) <= g} is one the
     * statement turns on only where the other part holds, and that is part of what a row at it has
     * to meet — so each line has a way of its own, the way to the comparison and where the line
     * decides after it.
     *
     * @param states which construct of the model the comparison is stated at
     * @param part   which of its lines and which case of where that line decides, where it states
     *               several; empty where it states one
     */
    public record ALine(ModelOccurrence states, Optional<WhereAPartDecides> part) {

        public ALine {
            Objects.requireNonNull(states, "a line is some comparison's");
            Objects.requireNonNull(part, "a line is the comparison's one, or one of several");
        }
    }

    /**
     * A condition as the walk met it — a truth a fork's condition asks, or a fork's whole
     * condition: what stood on the way to it, and what it coming out each way says
     * ({@link #stating}).
     *
     * <p>Both ways said here, where the condition and the reading of the input are in hand, so that
     * what is kept is what a row is composed against and compares as that.
     *
     * @param assumed what stood on the way to it
     * @param holding what it coming out true says
     * @param failing what it coming out false says
     */
    public record ConditionOnTheWay(List<OnTheWay> assumed, List<OnTheWay> holding,
                                    List<OnTheWay> failing) {

        public ConditionOnTheWay {
            assumed = List.copyOf(assumed);
            holding = List.copyOf(holding);
            failing = List.copyOf(failing);
        }
    }

    /**
     * What brings the truth the application {@code application} answers out {@code held}, where a
     * fork's condition asks it: every demand it coming out that way makes of a row, and the way to
     * it with those taken in — or empty where it asks something this reading could not state, asks
     * nothing, or no row takes the way.
     *
     * <p>The demands are on the way the row is held to and not only beside it. What a row has to
     * be for a truth to come out a way is a condition a composer meets the way it meets every
     * condition on the way to it, so the way it is held to is the way to the truth and the truth
     * itself. All of them, because a truth asks them all at once: some element meeting a predicate
     * and what the predicate asks of the rest of the row are one coming out.
     *
     * @param declarations what the declarations leave, which the way narrows
     */
    public Optional<HeldOutcome> heldAt(ModelOccurrence application, boolean held,
                                        SearchRegion declarations) {
        return held(byTruth.get(application), held, declarations);
    }

    /**
     * What brings a run down arm {@code part} of {@code fork}: the fork's whole condition coming
     * out the way the arm is taken on, as {@link #heldAt} answers it for an application.
     *
     * <p>A way past a guard names the arm where the condition has a part no construct of its own
     * records — the arm is where a run through it is seen. A run down the arm brought the whole
     * condition out that way, so that is what it takes of a row, whichever of its parts the way
     * also names; and where the condition coming out that way is nothing this can state, nothing
     * holds a row to the arm.
     */
    public Optional<HeldOutcome> heldAtTheArm(ModelOccurrence fork, int part,
                                              SearchRegion declarations) {
        return held(byFork.get(fork), part == 0, declarations);
    }

    private static Optional<HeldOutcome> held(ConditionOnTheWay met, boolean held,
                                              SearchRegion declarations) {
        if (met == null) {
            return Optional.empty();
        }
        List<OnTheWay> asked = held ? met.holding() : met.failing();
        List<RowDemand> demands = new ArrayList<>();
        for (OnTheWay each : asked) {
            switch (each) {
                case OnTheWay.TakenIn in -> demands.add(in.demand());
                case OnTheWay.Settled _ -> { }
                case OnTheWay.Declined _, OnTheWay.Narrowed _ -> {
                    return Optional.empty();
                }
            }
        }
        if (demands.isEmpty()) {
            return Optional.empty();
        }
        List<OnTheWay> way = new ArrayList<>(met.assumed());
        way.addAll(asked);
        return Reachability.of(new WayToTheBorder(way), declarations)
                instanceof Reachability.Reaching reaching
                ? Optional.of(new HeldOutcome(demands, reaching))
                : Optional.empty();
    }

    /**
     * How a row for a border on the line {@code origin} drew came to be looked for where it is: the
     * whole account of the walk to it, and where the line decides after it where it is one of
     * several a comparison states.
     *
     * <p>Empty where nothing was collected there — and the answer says so, rather than leaving a
     * reader to tell a comparison at the top of a body from one this could read nothing on the way
     * to. Both leave a region as wide as the declarations and both are sound; only one of them is a
     * limit of this compiler, and an author who is told nothing has no way to find out which they
     * are looking at.
     *
     * <p>Nothing on the way for a line no comparison drew. An invariant is about the values and
     * holds wherever one stands, and a clause states a relation the behavior is held to, so there
     * is nowhere for a row to have come from.
     */
    public WayToTheBorder wayTo(LineOrigin origin) {
        if (!(origin instanceof LineOrigin.ComparisonOrigin comparison)) {
            return WayToTheBorder.UNTOUCHED;
        }
        List<OnTheWay> found =
                byLine.get(new ALine(comparison.read().states(), comparison.part()));
        return new WayToTheBorder(found == null ? List.of() : found);
    }

    /**
     * What {@code node} coming out {@code holding} says about this input, and where it says
     * nothing, that.
     *
     * <p>Never empty. Every shape has an answer — a cut where one could be made and a decline
     * where none could — because an empty answer is what made a comparison reached under nothing
     * and one reached past something unreadable into the same reading.
     *
     * <p>One rule for two questions, because they are one question. What reaching the right operand
     * of a condition establishes and what reaching an arm of the fork establishes are both "this
     * subtree came out this way, so what follows" — written apart, the two agreed by having been
     * derived alike, and the day one of them learned to read a new shape of condition would be the
     * day they stopped agreeing.
     *
     * <p>A joined condition that came out the way its connective gives both halves is both halves
     * having come out that way, and which way that is comes from the composition under the outcome
     * rather than from the operator. The other composition says a disjunction of things, which is
     * not a list of cuts and is not approximated into one: {@code A && B} being false says one of
     * them failed and names neither, and narrowing on either would exclude rows that arrive. So it
     * is declined whole, at the condition rather than at an operand — neither operand is what could
     * not be carried.
     */
    static List<OnTheWay> stating(Condition node, InputReading read, boolean holding,
                                  WhatConditionsState conditions) {
        // What the condition asks is {@link DemandReading}'s, connectives and all, and each thing
        // it asks is put on the way at the condition of the shape that asked it. A truth stays
        // the truth it is: what a report names and where a run through it is seen are the
        // condition the author wrote, and only the demand is read as the comparison it means. A
        // disjunction of things is put at the whole node, since neither operand is what could not
        // be carried.
        return DemandReading.stated(node, read, holding, conditions).stream()
                .map(each -> onTheWay(each.where().occurrence(), each.where().anchor(),
                        each.read()))
                .toList();
    }

    /**
     * What reaching {@code arm} of {@code match} establishes about this input.
     *
     * <p>Beside {@link #stating} because it is the other half of one question. Both say what a row
     * that got here has already turned out to be; they differ in the vocabulary the answer lands in,
     * and a fork's answer is not a cut — which case a value is has no arithmetic and states nothing
     * about any order.
     *
     * <p><b>The narrowing and never the arm.</b> What a search can compose against is a position
     * read as one of its cases; "the second arm was taken" is a fact about the text. So what is
     * carried is the scrutinee's position with the arm's cases on it — the leaves under them where
     * a case is itself a sum — and where this reading cannot arrive at one — a scrutinee no position
     * holds, an arm over an optional's two carriers at once, a case the declarations leave no
     * position at — nothing is invented and the arm is declined.
     *
     * <p>And the narrowing is the one the checker's resolution of the arm settles, taken as it is
     * rather than built again from the case's name: the name says neither whether an optional's
     * present carrier or a sum's case was selected nor how many leaves selecting it covers, and a
     * narrowing spelled the wrong way is a position the reading of the input never holds.
     *
     * <p>Never empty, for the reason {@link #stating} is never empty: an arm that established
     * nothing and an arm nothing could be read of are the two answers a walk has to tell apart, and
     * a silence is both of them.
     */
    static OnTheWay entering(Core.Match match, Core.Case arm, int part, InputReading read,
                             InputReads reads, ConditionNumbering numbering) {
        InputDomain inputs = read.domain();
        RuleReadingSource ruleSource = read.rules();
        ConditionOccurrence met = numbering.metEntering(match, part);
        ConditionReportAnchor at =
                numbering.anchorOfArm(match.origin(), part, arm.pos(), met);
        // The selection whole, and not one narrowing made out of it: a case over several leaves
        // leaves the value several, and whether it narrows the position at all is the
        // declaration's to say below.
        CasesLeft selected = CasesLeft.selectedBy(arm.pattern());
        if (selected == null) {
            return new OnTheWay.Declined(met, at, new WhyNotTaken.ProjectionIncomplete(
                    WhyNotTaken.Shape.AN_ARM_READ_AS_WRITTEN));
        }
        // The arm is declined for either answer: a search composes against a position read as one
        // of its cases, and there is no position to narrow whether the scrutinee stands at none or
        // this reading did not follow it to one.
        TermPath scrutinee = switch (reads.forkedOn(match.scrutinee(), ruleSource.newtypes())) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            // And declined for a scrutinee that only may stand at one. What a narrowing is composed
            // against is one position; narrowing each of the ones it may be would say a row
            // reaching this arm stands at a case of every one of them, which is a region narrower
            // than the rows that arrive — the one direction that takes a coverage item away.
            case PathResolution.MayStandAt _ -> null;
        };
        // A value this reading already knows is no narrowing of anything, and needs none: every row
        // takes the arm or none does. Read before giving up on the position, since a scrutinee
        // standing at none is exactly what a helper handed a case written in the source matches.
        if (scrutinee == null) {
            Optional<Boolean> taken = reads.whetherEveryRowTakes(arm, match.scrutinee(),
                    ruleSource.symbols(), ruleSource.newtypes());
            if (taken.isPresent()) {
                return new OnTheWay.Settled(met, at, taken.get());
            }
        }
        // The position that is narrowed, and not the narrowed one. A case declaring no field has
        // nothing under it and this reading holds no position there, which is what it is for; what
        // has to exist is the position the case is a case of, since that is what a row writes a
        // value at and what a requirement on the way is keyed by.
        //
        // Two values and not one: where the name stands is what the environment answers, and
        // whether the input's rules hold a position there is the reading's.
        DeclaredInput.Taking taking = scrutinee == null ? null
                : taking(inputs, inputs.declared(ruleSource), scrutinee,
                        match.scrutinee().type(), selected);
        if (taking == null) {
            return new OnTheWay.Declined(met, at, new WhyNotTaken.ProjectionIncomplete(
                    WhyNotTaken.Shape.AN_ARM_READ_AS_WRITTEN));
        }
        return switch (taking) {
            case DeclaredInput.Taking.Narrows(TermPath to) -> new OnTheWay.Narrowed(at, to,
                    inputs.reach().crossings(), onItsOrder(to, read));
            case DeclaredInput.Taking.Implied _ -> new OnTheWay.Settled(met, at, true);
            case DeclaredInput.Taking.Excluded _ -> new OnTheWay.Settled(met, at, false);
        };
    }

    /**
     * What arriving at an arm leaving {@code selected} says of the value at {@code scrutinee}, or
     * null where this reading cannot say.
     *
     * <p>The case is relative to the type the scrutinee stands as, and the value there may be
     * narrower: what the declaration puts at the position says whether reaching the arm narrows it,
     * or comes out one way for every row because the declaration already decided.
     *
     * <p><b>At a name the cases of a sum share, asked under each case.</b> The value there stands
     * at one position under each case the row can be ({@link WhereANameIsWritten}), and what the
     * declarations leave it may differ from one case to the next. The arm narrows the name where it
     * narrows the value under some case, to the cases it leaves under any of them; it is settled
     * only where it is settled the same way under every case. A case whose reading stopped before
     * putting the name anywhere is a place whose declarations were never read, so nothing is said
     * there rather than an answer made out of the cases that were.
     */
    private static DeclaredInput.Taking taking(InputDomain inputs, DeclaredInput declared,
                                               TermPath scrutinee, Type matchedAs,
                                               CasesLeft selected) {
        if (held(inputs, scrutinee)) {
            return declared.taking(scrutinee, matchedAs, selected);
        }
        WhereANameIsWritten under = WhereANameIsWritten.ofAName(inputs, scrutinee);
        if (under == null) {
            return null;
        }
        Set<Refinement> left = new LinkedHashSet<>();
        boolean implied = true;
        for (WhereANameIsWritten.Place place : under.places()) {
            switch (declared.taking(place.position(), matchedAs, selected)) {
                case DeclaredInput.Taking.Narrows(TermPath to) -> {
                    left.addAll(to.narrowing().atoms());
                    implied = false;
                }
                case DeclaredInput.Taking.Implied _ -> left.addAll(selected.atoms());
                case DeclaredInput.Taking.Excluded _ -> implied = false;
            }
        }
        if (implied) {
            return new DeclaredInput.Taking.Implied();
        }
        CasesLeft kept = selected.keeping(left::contains);
        return kept == null ? new DeclaredInput.Taking.Excluded()
                : new DeclaredInput.Taking.Narrows(DeclaredInput.narrowedTo(scrutinee, kept));
    }

    /**
     * What {@code narrowed} says on the order of the position it narrows: a hole at each case of
     * the enumeration the narrowing leaves out, and nothing where no enumeration orders the
     * position.
     *
     * <p>Asked of the reading, which is what says which order a position stands on — the same
     * question a comparison of the position against a written case is read through, so that the
     * places a narrowing leaves out are the places a comparison names.
     */
    private static List<TakenConstraint.AwayFrom> onItsOrder(TermPath narrowed, InputReading read) {
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(narrowed.narrowedFrom().position());
        TermOrders orders = read.quantities().ordersOf(term);
        if (orders == null || !(orders.answered() instanceof Carrier.Ordinal ordinal)) {
            return List.of();
        }
        List<TakenConstraint.AwayFrom> out = new ArrayList<>();
        for (TypeSymbol each : ordinal.cases()) {
            if (!narrowed.narrowing().leaves(each)) {
                out.add(new TakenConstraint.AwayFrom(term, ordinal.at(each)));
            }
        }
        return List.copyOf(out);
    }

    /**
     * What the arms of {@code match} leave the scrutinee, one entry per arm that is a column.
     *
     * <p>The question a fork asks, as the answers it has. Two forks over one position can ask two
     * questions — whether a visit is a {@code OnceKind} or a {@code Renkei}, and inside the first,
     * whether it is a {@code Station} or a {@code Hospital} — and a rule through both answers each of
     * them, so what tells the two columns apart is which answers each fork has and not the position
     * they are about. Two forks dividing a position the same way are one question, wherever each is
     * written.
     *
     * <p>Each answer is the one the arm is read as ({@link #entering}): the cases the declaration
     * leaves of the ones the arm covers where it narrows the position, and the cases the arm covers
     * where the declaration leaves it none of them or where no position is narrowed. An arm the
     * declaration already decides is no column and no answer, and neither is an arm over an
     * optional's two carriers at once.
     */
    static Set<CasesLeft> answersOf(Core.Match match, InputDomain inputs, InputReads reads,
                                    RuleReadingSource ruleSource) {
        TermPath scrutinee = reads.forkedOn(match.scrutinee(), ruleSource.newtypes())
                instanceof PathResolution.At(var stands) ? stands : null;
        DeclaredInput declared = scrutinee == null ? null : inputs.declared(ruleSource);
        Set<CasesLeft> out = new LinkedHashSet<>();
        for (Core.Case arm : match.cases()) {
            CasesLeft selected = CasesLeft.selectedBy(arm.pattern());
            if (selected == null) {
                continue;
            }
            DeclaredInput.Taking taking = declared == null ? null
                    : taking(inputs, declared, scrutinee, match.scrutinee().type(), selected);
            if (taking == null) {
                out.add(selected);
                continue;
            }
            switch (taking) {
                case DeclaredInput.Taking.Narrows(TermPath to) -> out.add(to.narrowing());
                case DeclaredInput.Taking.Excluded _ -> out.add(selected);
                case DeclaredInput.Taking.Implied _ -> { }
            }
        }
        return out;
    }

    /** Whether the input's rules hold the position a fork on {@code scrutinee} narrows
     *  ({@link TermPath#position}). */
    private static boolean held(InputDomain inputs, TermPath scrutinee) {
        return inputs.at(scrutinee.position()) != null;
    }

    /**
     * What reaching arm {@code part} of {@code attempt} establishes about this input, which this
     * reading cannot say.
     *
     * <p>The arm is decided by whether the construction's invariant held of the values it was
     * given, and what that says of the input is the invariant read over those values. That is a
     * reading of the invariant and not of anything this walk met, so the arm is declined rather than
     * given a narrowing the walk did not establish. Declined and not left out: a rule through the
     * arm still turns on it, and it is named so that the success and each departure are distinctions
     * apart.
     *
     * @param at where the arm is written, which is its body since an attempt writes no arm of its own
     */
    static OnTheWay attempting(Core.IfConstructed attempt, int part, SourcePos at,
                               ConditionNumbering numbering) {
        ConditionOccurrence met = numbering.metEntering(attempt, part);
        return new OnTheWay.Declined(met, numbering.anchorOfArm(attempt.origin(), part, at, met),
                new WhyNotTaken.ProjectionIncomplete(WhyNotTaken.Shape.AN_ARM_AN_INVARIANT_DECIDES));
    }

    /**
     * What a line of the comparison {@code at} asks of a row for the statement to turn on it,
     * {@code decides}, put on the way at that comparison.
     *
     * <p>At the comparison, because that is where it was written: what has to hold beside a line
     * is part of what the comparison states. A part of it this reading has no words for is
     * declined there with whatever stopped it, as any condition on the way is — so a line looked
     * for over rows where it may decide nothing says so, and is never taken to be one nothing
     * reaches for it.
     */
    static List<OnTheWay> whereItDecides(Condition at, Proposition decides, InputReading read) {
        return DemandReading.asked(decides, read).stream()
                .map(each -> onTheWay(at.occurrence(), at.anchor(), each))
                .toList();
    }

    /**
     * What a condition's demand comes to on the way: taken in where there is one, and declined at
     * the condition with the reason where there is none.
     */
    private static OnTheWay onTheWay(ConditionOccurrence condition, ConditionReportAnchor at,
                                     DemandReading.Read read) {
        return switch (read) {
            case DemandReading.Read.Demands(var demand) -> new OnTheWay.TakenIn(at, demand);
            case DemandReading.Read.Settled(var thisWay) ->
                    new OnTheWay.Settled(condition, at, thisWay);
            case DemandReading.Read.Unread(var why) -> new OnTheWay.Declined(condition, at, why);
        };
    }

    /** These conditions, with the rule stated at {@code states} reached under {@code assumed}. */
    static final class Collected {

        private final Map<ALine, List<OnTheWay>> byLine = new LinkedHashMap<>();
        private final Map<ModelOccurrence, ConditionOnTheWay> byTruth = new LinkedHashMap<>();
        private final Map<ModelOccurrence, ConditionOnTheWay> byFork = new LinkedHashMap<>();

        /**
         * The truth the application {@code answers} answers, met as {@code met} says.
         *
         * <p>Once per construct of the model, as a comparison is, and for the same reason: two
         * arriving under one would be two truths the model states at one place.
         */
        void answered(ModelOccurrence answers, ConditionOnTheWay met) {
            if (byTruth.putIfAbsent(answers, met) != null) {
                throw new IllegalStateException(
                        "two truths of one reading state one construct of the model: " + answers);
            }
        }

        /**
         * The whole condition of {@code fork}, met as {@code met} says.
         *
         * <p>Once per fork, since a fork has one condition. A fork inside a non-recursive helper is
         * read once per call of it, and each of those is a fork of its own.
         */
        void decides(ModelOccurrence fork, ConditionOnTheWay met) {
            if (byFork.putIfAbsent(fork, met) != null) {
                throw new IllegalStateException(
                        "two conditions of one reading decide one fork of the model: " + fork);
            }
        }

        /**
         * The comparison stated at {@code states}, reached under {@code assumed} — and each reading
         * of each of its lines, where it states several, reached under that and then the case of
         * where the line decides it is read in.
         */
        void reached(ModelOccurrence states, List<OnTheWay> assumed,
                     Map<WhereAPartDecides, List<OnTheWay>> whereEachDecides) {
            // Once per construct of the model, because that is what the walk reads: a comparison
            // inside a non-recursive helper is read once per call of it and each of those calls is
            // a construct of its own. Two arriving under one would be the reading holding two
            // comparisons the model states at one place, which is what nothing downstream could
            // then tell apart — so it is refused here rather than resolved by keeping one of them.
            List<OnTheWay> already =
                    byLine.putIfAbsent(new ALine(states, Optional.empty()), List.copyOf(assumed));
            if (already != null) {
                throw new IllegalStateException(
                        "two comparisons of one reading state one construct of the model: "
                                + states);
            }
            whereEachDecides.forEach((part, decides) -> {
                List<OnTheWay> way = new ArrayList<>(assumed);
                way.addAll(decides);
                byLine.put(new ALine(states, Optional.of(part)), List.copyOf(way));
            });
        }

        ReachingCuts made() {
            return new ReachingCuts(Lookup.built(put -> byLine.forEach(put::put)),
                    Lookup.built(put -> byTruth.forEach(put::put)),
                    Lookup.built(put -> byFork.forEach(put::put)));
        }
    }
}
