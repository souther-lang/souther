package souther.compiler.partition;

import souther.compiler.carrier.Lookup;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.core.Core;
import souther.compiler.core.EnteredArm;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiPredicate;

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
                           Lookup<ALine, SaidOnTheWay> saidByLine,
                           Lookup<ModelOccurrence, List<ConditionOnTheWay>> byOutcome,
                           Lookup<ModelOccurrence, ConditionOnTheWay> byFork) {

    public static final ReachingCuts NONE = new ReachingCuts(Lookup.built(_ -> { }),
            Lookup.built(_ -> { }), Lookup.built(_ -> { }), Lookup.built(_ -> { }));

    public ReachingCuts {
        Objects.requireNonNull(byLine, "what a walk collected, line by line");
        Objects.requireNonNull(saidByLine, "who put what on each line's way");
        Objects.requireNonNull(byOutcome,
                "what a walk collected, truth by truth and comparison by comparison");
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
     * What brings the truth or the comparison the construct {@code application} answers out
     * {@code held}, where a fork's condition asks it: every demand it coming out that way makes of
     * a row, and the way to it with those taken in — or nothing found where it asks something this
     * reading could not state, asks nothing, or no row takes the way.
     *
     * <p>The demands are on the way the row is held to and not only beside it. What a row has to
     * be for a truth to come out a way is a condition a composer meets the way it meets every
     * condition on the way to it, so the way it is held to is the way to the truth and the truth
     * itself. All of them, because a truth asks them all at once: some element meeting a predicate
     * and what the predicate asks of the rest of the row are one coming out.
     *
     * <p>And where what it asks is one of several things, one of them at a time
     * ({@link HeldOutcome.Bringing.Found}).
     *
     * @param declarations what the declarations leave, which the way narrows
     */
    public HeldOutcome.Bringing heldAt(ModelOccurrence application, boolean held,
                                       SearchRegion declarations) {
        List<ConditionOnTheWay> copies = byOutcome.get(application);
        if (copies == null) {
            return new HeldOutcome.Bringing.NothingFound();
        }
        // Each copy a way of its own, in the order the walk met them, and two copies met alike
        // one way: told apart here, where one condition is asked, and not where every condition
        // is filed.
        List<HeldOutcome.Bringing> each = new ArrayList<>();
        for (ConditionOnTheWay copy : copies.size() == 1 ? copies
                : List.copyOf(new LinkedHashSet<>(copies))) {
            each.add(held(copy, held, declarations));
        }
        return HeldOutcome.Bringing.oneOf(each);
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
    public HeldOutcome.Bringing heldAtTheArm(ModelOccurrence fork, int part,
                                             SearchRegion declarations) {
        return held(byFork.get(fork), part == 0, declarations);
    }

    /**
     * What {@code met} coming out {@code held} asks of a row, as one way for each way some row
     * may take past it.
     *
     * <p>What it asks is walked as a way is ({@link WayToTheBorder#along}), so that what is one of
     * several things is each of them in turn, and a row is held to one of them. And each is held
     * along the way to the condition taken the same way: a guard above that came out one of
     * several ways is past along one of them, and a row composed against the way whole is
     * composed against none of what that guard asked. So each alternative is held along every way
     * the way to it splits into, and along the way whole after them, which every row past it is
     * on.
     *
     * <p>The way whole first, and the ways it splits into after it. A row composed along the way
     * whole is composed against less, and found there is a row past the condition all the same;
     * the ways it splits into are each more of what was asked, looked along where the whole came
     * to nothing.
     *
     * <p>Each alternative's answer is its own, and they are put together by the one law for it
     * ({@link HeldOutcome.Bringing#oneOf}): an alternative asking something this reading could not
     * state, or nothing, is this compiler's to have fallen short on; one no row takes is the
     * model's; and a figure that stopped the walk is said with the figure. What is asked is
     * walked to the end or the figure is said: a walk that closed proves no row has the condition
     * come out so.
     */
    private static HeldOutcome.Bringing held(ConditionOnTheWay met, boolean held,
                                             SearchRegion declarations) {
        if (met == null) {
            return new HeldOutcome.Bringing.NothingFound();
        }
        List<OnTheWay> asked = held ? met.holding() : met.failing();
        List<OnTheWay> onTheWay = new ArrayList<>(met.assumed());
        onTheWay.addAll(asked);
        WayToTheBorder whole = new WayToTheBorder(onTheWay);
        List<HeldOutcome.Bringing> each = new ArrayList<>();
        switch (new WayToTheBorder(asked).along()) {
            case OneOfEach.Walked.Closed<OnTheWay, Reachability> _ -> {
                return new HeldOutcome.Bringing.NoValueCanStandThere();
            }
            case OneOfEach.Walked.Stopped<OnTheWay, Reachability>(var figure) -> {
                return new HeldOutcome.Bringing.LeftUnlooked(Set.of(figure));
            }
            case OneOfEach.Walked.Open<OnTheWay, Reachability>(var alternatives, var stoppedBy) -> {
                if (stoppedBy != null) {
                    each.add(new HeldOutcome.Bringing.LeftUnlooked(Set.of(stoppedBy)));
                }
                for (OneOfEach.Way<OnTheWay> alternative : alternatives) {
                    // An alternative whose choices the figure left is not what the condition
                    // asks, and the figure is said above.
                    if (alternative instanceof OneOfEach.Way.Chosen<OnTheWay>(var entries,
                            var choices)) {
                        each.add(alongEach(whole, entries, HeldOutcome.byCondition(choices),
                                declarations));
                    }
                }
            }
        }
        return HeldOutcome.Bringing.oneOf(each);
    }

    /**
     * One alternative of what a condition asks, {@code asks}, the choices {@code choices} names
     * taken on the way {@code whole}: held along the way whole first, and along every way the way
     * to it splits into after it.
     *
     * <p>What the alternative asks in each vocabulary it asks in: the demands a composer composes
     * toward, and the cases a value is, which a composer meets as the way's requirements and
     * which holding a row to them writes. Only a condition this reading could not state leaves it
     * nothing to hold a row to.
     *
     * <p>The way whole first because a row composed along it is composed against less, and found
     * there is a row past the condition all the same; each way it splits into is more of what was
     * asked, looked along where the whole came to nothing. Each split way is named by the choices
     * it takes, so that a guard below takes them the same way.
     */
    private static HeldOutcome.Bringing alongEach(WayToTheBorder whole, List<OnTheWay> asks,
                                                  Map<OnTheWay, Set<Integer>> choices,
                                                  SearchRegion declarations) {
        List<RowDemand> demands = new ArrayList<>();
        List<OnTheWay.Narrowed> cases = new ArrayList<>();
        for (OnTheWay each : asks) {
            switch (each) {
                case OnTheWay.TakenIn in -> demands.add(in.demand());
                case OnTheWay.Narrowed narrowed -> cases.add(narrowed);
                case OnTheWay.Settled _ -> { }
                // Which of the statements counted hold is not chosen here, so what the alternative
                // brings is not said.
                case OnTheWay.Declined _, OnTheWay.Counted _ -> {
                    return new HeldOutcome.Bringing.NothingFound();
                }
                case OnTheWay.OneOf _ -> throw new IllegalStateException(
                        "an alternative with every choice chosen asks no choice: " + each);
            }
        }
        if (demands.isEmpty() && cases.isEmpty()) {
            return new HeldOutcome.Bringing.NothingFound();
        }
        WayToTheBorder taken = whole.choosing(choices);
        if (!(Reachability.of(taken, declarations) instanceof Reachability.Reaching reaching)) {
            return new HeldOutcome.Bringing.NoValueCanStandThere();
        }
        List<HeldOutcome> ways = new ArrayList<>();
        ways.add(new HeldOutcome(demands, cases, whole, choices, reaching));
        CompositionBudget figure = null;
        switch (taken.along()) {
            case OneOfEach.Walked.Open<OnTheWay, Reachability>(var split, var stoppedBy) -> {
                figure = stoppedBy;
                for (OneOfEach.Way<OnTheWay> one : split) {
                    if (!(one instanceof OneOfEach.Way.Chosen<OnTheWay>(var _, var more))
                            || more.isEmpty()) {
                        continue;
                    }
                    Map<OnTheWay, Set<Integer>> both = new LinkedHashMap<>();
                    choices.forEach((condition, alternatives) -> both.put(condition,
                            new TreeSet<>(alternatives)));
                    HeldOutcome.byCondition(more).forEach((condition, alternatives) -> both
                            .computeIfAbsent(condition, _ -> new TreeSet<>())
                            .addAll(alternatives));
                    if (Reachability.of(whole.choosing(both), declarations)
                            instanceof Reachability.Reaching along) {
                        ways.add(new HeldOutcome(demands, cases, whole, both, along));
                    }
                }
            }
            case OneOfEach.Walked.Stopped<OnTheWay, Reachability>(var stoppedBy) ->
                    figure = stoppedBy;
            case OneOfEach.Walked.Closed<OnTheWay, Reachability> _ -> throw new IllegalStateException(
                    "a way the reading found open is one its walk finds open: " + taken);
        }
        return new HeldOutcome.Bringing.Found(ways,
                figure == null ? Set.of() : Set.of(figure));
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
     * How a row for a class that the line {@code origin} cuts came to be looked for where it is:
     * the walk to the comparison, without the case of where the line decides it.
     *
     * <p>A region to look in that contains the one {@link #wayTo} gives. The case is where the
     * line turns the statement, and the classes it cuts run over the whole of the quantity: a
     * value in a class outside the case reaches the comparison and answers it. Whether a row there
     * is a row of the class is the run's to say, by the answer the comparison came out with.
     */
    public WayToTheBorder wayToTheComparison(LineOrigin origin) {
        if (!(origin instanceof LineOrigin.ComparisonOrigin comparison)) {
            return WayToTheBorder.UNTOUCHED;
        }
        List<OnTheWay> found =
                byLine.get(new ALine(comparison.read().states(), Optional.empty()));
        return new WayToTheBorder(found == null ? List.of() : found);
    }

    /**
     * Whether no row is on the ways to the lines {@code one} and {@code other} at once: what the two
     * ways ask of a row, taken together, asks one position to be two things.
     *
     * <p>Then a row at one of them is never at the other, and the other's place is no edge of a run
     * beside the first. {@code month.value <= minimum(term)} draws its line at 12 where {@code term}
     * is {@code OneYear} and at 24 where it is {@code TwoYear}; a row at the first has a month above
     * 24 on the same side of 12 as one at 13.
     *
     * <p>Only a proof says so. Nothing is said where either way is one of several ways, or where the
     * position asked twice is inside the elements or keys of a container: two comparisons inside two
     * closures each ask that of an element of their own, which may be two elements of one row.
     *
     * <p>Asked of the cases and the truths the two ways ask, which are the two things a way asks a
     * position to be ({@link Reachability.TwoAtOnce}); the region the ways leave is not worked out,
     * since nothing here reads it.
     */
    public boolean neverTogether(LineOrigin one, LineOrigin other) {
        WayToTheBorder first = wayTo(one);
        WayToTheBorder second = wayTo(other);
        if (first.onTheWay().isEmpty() || second.onTheWay().isEmpty()
                || !first.severalWays().isEmpty() || !second.severalWays().isEmpty()) {
            return false;
        }
        List<OnTheWay> joined = new ArrayList<>(first.onTheWay());
        joined.addAll(second.onTheWay());
        WayToTheBorder both = new WayToTheBorder(joined);
        TermPath twice = switch (both.requirements()) {
            case Requirements.Merge.Conflict conflict -> conflict.at();
            case Requirements.Merge.Merged _ ->
                    both.truths() instanceof TruthsAsked.Merge.Conflict(TermPath at) ? at : null;
        };
        return twice != null && twice.steps().stream().noneMatch(step ->
                step instanceof TermPath.Step.Element || step instanceof TermPath.Step.Key);
    }

    /**
     * {@link #neverTogether}, asked of each pair of lines once however many borders ask it: a
     * border asks it of every other line on its quantity, and every line on the quantity is a
     * border.
     */
    public BiPredicate<LineOrigin, LineOrigin> apart() {
        Map<LineOrigin, Map<LineOrigin, Boolean>> asked = new IdentityHashMap<>();
        return (one, other) -> {
            Boolean before = asked.getOrDefault(other, Map.of()).get(one);
            return before != null ? before : asked.computeIfAbsent(one, _ -> new IdentityHashMap<>())
                    .computeIfAbsent(other, _ -> neverTogether(one, other));
        };
    }

    /**
     * Which copies of the model's code put each entry on the way to the line {@code origin} drew
     * ({@link #wayTo}), told when the ways to it were walked and of those ways alone.
     */
    public SaidOnTheWay saidOnTheWayTo(LineOrigin origin) {
        if (!(origin instanceof LineOrigin.ComparisonOrigin comparison)) {
            return SaidOnTheWay.NONE;
        }
        SaidOnTheWay said =
                saidByLine.get(new ALine(comparison.read().states(), comparison.part()));
        return said == null ? SaidOnTheWay.NONE : said;
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
    static Stating stating(Condition node, InputReading read, boolean holding,
                           WhatConditionsState conditions) {
        // What the condition asks is {@link DemandReading}'s, connectives and all, and each thing
        // it asks is put on the way at the condition of the shape that asked it. A truth stays
        // the truth it is: what a report names and where a run through it is seen are the
        // condition the author wrote, and only the demand is read as the comparison it means. A
        // disjunction of things is put at the whole node, since neither operand is what could not
        // be carried.
        List<OnTheWay> entries = new ArrayList<>();
        Map<OnTheWay, ModelOccurrences> by = new LinkedHashMap<>();
        for (DemandReading.Stated each : DemandReading.stated(node, read, holding, conditions)) {
            entries.add(onTheWay(each.where().occurrence(), each.where().anchor(), each.read(),
                    read, each.readOff(), by, Optional.empty()));
        }
        return new Stating(entries, new SaidOnTheWay(by, Map.of(), Map.of()));
    }

    /**
     * What a condition put on the way, and which copies of the model's code each entry was read
     * off.
     *
     * <p>Told where the entries are made, which is the one place the part each was read off is
     * still known. An entry is filed under a condition of the shape, and the condition is no
     * account of where each thing it asks was read: a comparison over what another call of a
     * helper worked out asks what that call's fork decided, and the halves of a joined condition
     * may stand in two calls.
     *
     * @param entries what was put on the way, in order
     * @param by      which copies each entry and each entry inside an alternative of one was read
     *                off
     */
    record Stating(List<OnTheWay> entries, SaidOnTheWay by) {

        Stating {
            entries = List.copyOf(entries);
            Objects.requireNonNull(by, "which copies each entry was read off, or none");
        }

        /** {@code entries}, every one of them and of their alternatives read off
         *  {@code readIn}. */
        static Stating of(List<OnTheWay> entries, ModelOccurrences readIn) {
            Map<OnTheWay, ModelOccurrences> by = new LinkedHashMap<>();
            SaidOnTheWay.filed(entries, readIn, by);
            return new Stating(entries, new SaidOnTheWay(by, Map.of(), Map.of()));
        }
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
    static Stating entering(Core.Match match, Core.Case arm, int part, InputReading read,
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
            return enteredWhole(match, part, read, reads, met, at);
        }
        // The arm is declined for either answer: a search composes against a position read as one
        // of its cases, and there is no position to narrow whether the scrutinee stands at none or
        // this reading did not follow it to one.
        TermPath scrutinee = positionOf(match, reads, ruleSource);
        // A value this reading already knows is no narrowing of anything, and needs none: every row
        // takes the arm or none does. Read before giving up on the position, since a scrutinee
        // standing at none is exactly what a helper handed a case written in the source matches.
        if (scrutinee == null) {
            Optional<Boolean> taken = reads.whetherEveryRowTakes(arm, match.scrutinee(),
                    ruleSource.symbols(), ruleSource.newtypes());
            if (taken.isPresent()) {
                return Stating.of(List.of(new OnTheWay.Settled(met, at, taken.get())),
                        copyOf(match.occurrence()));
            }
        }
        // The position that is narrowed, and not the narrowed one. A case declaring no field has
        // nothing under it and this reading holds no position there, which is what it is for; what
        // has to exist is the position the case is a case of, since that is what a row writes a
        // value at and what a requirement on the way is keyed by.
        DeclaredInput.Taking taking = takingAt(match, scrutinee, selected, read);
        if (taking == null) {
            return enteredWhole(match, part, read, reads, met, at);
        }
        // What the fork states of its own scrutinee, read off the copy it stands in.
        return Stating.of(List.of(switch (taking) {
            case DeclaredInput.Taking.Narrows(TermPath to) -> new OnTheWay.Narrowed(at, to,
                    inputs.reach().crossings(), onItsOrder(to, read));
            case DeclaredInput.Taking.Implied _ -> new OnTheWay.Settled(met, at, true);
            case DeclaredInput.Taking.Excluded _ -> new OnTheWay.Settled(met, at, false);
        }), copyOf(match.occurrence()));
    }

    /**
     * The one position the scrutinee of {@code match} stands at, or null where it stands at none.
     *
     * <p>Null both where the scrutinee stands at none and where this reading did not follow it to
     * one. And for a scrutinee that only may stand at one: what a narrowing is composed against is
     * one position, and narrowing each of the ones it may be would say a row reaching an arm
     * stands at a case of every one of them, which is a region narrower than the rows that arrive
     * — the one direction that takes a coverage item away.
     */
    private static TermPath positionOf(Core.Match match, InputReads reads,
                                       RuleReadingSource ruleSource) {
        return switch (reads.forkedOn(match.scrutinee(), ruleSource.newtypes())) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
        };
    }

    /**
     * What arriving at an arm leaving {@code selected} says of the position {@code scrutinee}
     * stands at, or null where there is no position to say it of.
     *
     * <p>The position that is narrowed, and not the narrowed one. A case declaring no field has
     * nothing under it and this reading holds no position there, which is what it is for; what has
     * to exist is the position the case is a case of, since that is what a row writes a value at
     * and what a requirement on the way is keyed by.
     *
     * <p>Two values and not one: where the name stands is what the environment answers, and
     * whether the input's rules hold a position there is the reading's.
     */
    private static DeclaredInput.Taking takingAt(Core.Match match, TermPath scrutinee,
                                                 CasesLeft selected, InputReading read) {
        return scrutinee == null ? null
                : taking(read.domain(), read.domain().declared(read.rules()), scrutinee,
                        match.scrutinee().type(), selected);
    }

    /**
     * Whether arm {@code arm} of {@code match} narrows the position its own scrutinee stands at, so
     * that what {@link #entering} puts on the way for it is an answer to the question the fork
     * asks. Otherwise the arm is read whole ({@link #enteredWhole}): what it comes to for the
     * input is no answer to a fork on a value the body computed.
     *
     * <p>Decided by the same two readings {@link #entering} decides by, so the two cannot differ
     * about which arm is which.
     */
    static boolean narrowsItsOwnPosition(Core.Match match, Core.Case arm, InputReading read,
                                         InputReads reads) {
        CasesLeft selected = CasesLeft.selectedBy(arm.pattern());
        return selected != null && takingAt(match, positionOf(match, reads, read.rules()),
                selected, read) instanceof DeclaredInput.Taking.Narrows;
    }

    /**
     * What entering arm {@code part} of {@code match} asks of a row where it narrows no one
     * position: what the arm states ({@link Pullback#ofTheArms}) — which case a value a helper or
     * another behavior answers is, under what; an optional's two carriers at once — asked as any
     * condition is.
     */
    private static Stating enteredWhole(Core.Match match, int part, InputReading read,
                                        InputReads reads, ConditionOccurrence met,
                                        ConditionReportAnchor at) {
        return armStated(WhatConditionsState.of(read).arm(match, part, reads), met, at, read,
                copyOf(match.occurrence()), EnteredArm.of(match.cases().get(part)));
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
    static List<TakenConstraint.AwayFrom> onItsOrder(TermPath narrowed, InputReading read) {
        NumericTerm.ValueOf term = new NumericTerm.ValueOf(narrowed.narrowedFrom().position());
        TermOrders orders = read.quantities().ordersOf(term);
        if (orders == null || !(orders.answered() instanceof Carrier.Ordinal ordinal)) {
            return List.of();
        }
        Set<TypeSymbol> left = narrowed.narrowing().leavesOfASum();
        return ordinal.placesOf(each -> !left.contains(each)).stream()
                .map(at -> new TakenConstraint.AwayFrom(term, at))
                .toList();
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
     * What reaching arm {@code part} of {@code attempt} establishes about this input: what the arm
     * states ({@link Pullback#ofTheArms}) — the clauses of the invariant it checks, read over the
     * values the attempt hands it — asked of a row as any condition is.
     *
     * @param at where the arm is written, which is its body since an attempt writes no arm of its own
     */
    static Stating attempting(Core.IfConstructed attempt, int part, SourcePos at,
                              InputReading read, InputReads reads,
                              ConditionNumbering numbering) {
        ConditionOccurrence met = numbering.metEntering(attempt, part);
        return armStated(WhatConditionsState.of(read).arm(attempt, part, reads), met,
                numbering.anchorOfArm(attempt.origin(), part, at, met), read,
                copyOf(attempt.occurrence()), Optional.empty());
    }

    /**
     * What a run entering an arm that states what {@code arm} read asks of a row, each thing it
     * asks put on the way at the arm, and read off the parts of what the arm states — what the
     * fork itself states read off {@code fork}, the copy it stands in.
     *
     * @param entered the arm of the match that is entered, where it is one
     */
    private static Stating armStated(Pullback.Pulled arm, ConditionOccurrence met,
                                     ConditionReportAnchor at, InputReading read,
                                     ModelOccurrences fork, Optional<EnteredArm> entered) {
        DemandReading.Projected made =
                DemandReading.projectedOff(arm, arm.proposition(), read, fork);
        List<OnTheWay> entries = new ArrayList<>();
        Map<OnTheWay, ModelOccurrences> by = new LinkedHashMap<>();
        for (DemandReading.Read each : made.reads()) {
            entries.add(onTheWay(met, at, each, read, made.readOff(), by, entered));
        }
        return new Stating(entries, new SaidOnTheWay(by, Map.of(), Map.of()));
    }

    /** The copy of the model's code {@code fork} stands in, or none where the model states
     *  nothing there. */
    private static ModelOccurrences copyOf(ConstructOccurrence fork) {
        return fork.isWritten()
                ? ModelOccurrence.statedAt(fork).map(ModelOccurrences::of)
                        .orElse(ModelOccurrences.NONE)
                : ModelOccurrences.NONE;
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
    static Stating whereItDecides(Condition at, Proposition decides, InputReading read) {
        // Read off the parts of the comparison's own statement: where a line decides is a fact of
        // the comparison, over the values it reads.
        List<OnTheWay> entries = new ArrayList<>();
        Map<OnTheWay, ModelOccurrences> by = new LinkedHashMap<>();
        for (DemandReading.Stated each
                : DemandReading.askedAt(at, decides, read, WhatConditionsState.of(read))) {
            entries.add(onTheWay(at.occurrence(), at.anchor(), each.read(), read, each.readOff(),
                    by, Optional.empty()));
        }
        return new Stating(entries, new SaidOnTheWay(by, Map.of(), Map.of()));
    }

    /**
     * What a condition's demand comes to on the way: taken in where there is one, and declined at
     * the condition with the reason where there is none.
     *
     * <p>And which copies of the model's code it was read off, filed into {@code by} as it is
     * made: what {@code readOff} says of the read, and of each read inside an alternative of it.
     */
    private static OnTheWay onTheWay(ConditionOccurrence condition, ConditionReportAnchor at,
                                     DemandReading.Read read, InputReading input,
                                     DemandReading.ReadOff readOff,
                                     Map<OnTheWay, ModelOccurrences> by,
                                     Optional<EnteredArm> entered) {
        OnTheWay made = switch (read) {
            case DemandReading.Read.Demands(var demand) -> new OnTheWay.TakenIn(at, demand);
            case DemandReading.Read.Settled(var thisWay) ->
                    new OnTheWay.Settled(condition, at, thisWay);
            case DemandReading.Read.Narrows(TermPath position, CasesLeft cases) ->
                    narrowing(condition, at, position, cases, input);
            case DemandReading.Read.OneOf oneOf -> OnTheWay.OneOf.of(
                    condition, at, oneOf.alternatives().stream().map(each -> each.stream()
                            .map(one -> onTheWay(condition, at, one, input, readOff, by, entered))
                            .toList()).toList(),
                    oneOf.stated());
            case DemandReading.Read.Counted counted -> new OnTheWay.Counted(condition, at,
                    counted.statements().stream().map(each -> new OnTheWay.Counted.Statement(
                            each.weight(),
                            each.holding().stream().map(one -> onTheWay(condition, at, one, input,
                                    readOff, by, entered)).toList(),
                            each.failing().stream().map(one -> onTheWay(condition, at, one, input,
                                    readOff, by, entered)).toList())).toList(),
                    counted.admitted(), counted.stated());
            case DemandReading.Read.Unread(var whys, var besideAnAnswer) ->
                    new OnTheWay.Declined(condition, at, whys, entered, besideAnAnswer);
        };
        SaidOnTheWay.filedAlone(made, readOff.of(read), by);
        return made;
    }

    /**
     * The value at {@code position} read as one of {@code cases}, as what the declarations leave it
     * says: a narrowing where they leave it more than those, and settled where they leave it only
     * those or none of them ({@link #taking}).
     */
    private static OnTheWay narrowing(ConditionOccurrence condition, ConditionReportAnchor at,
                                      TermPath position, CasesLeft cases, InputReading read) {
        InputDomain inputs = read.domain();
        return switch (taking(position, cases, read)) {
            case DeclaredInput.Taking.Narrows(TermPath to) -> new OnTheWay.Narrowed(at, to,
                    inputs.reach().crossings(), onItsOrder(to, read));
            case DeclaredInput.Taking.Implied _ -> new OnTheWay.Settled(condition, at, true);
            case DeclaredInput.Taking.Excluded _ -> new OnTheWay.Settled(condition, at, false);
        };
    }

    /**
     * What the value at {@code position} read as one of {@code cases} comes to, as what the
     * declarations leave it says ({@link #taking(InputDomain, DeclaredInput, TermPath, Type,
     * CasesLeft)}).
     *
     * <p>Asked where the value is one an element holds as much as where a way passes a fork on
     * it: the declarations leave a position inside an element what they leave every element.
     *
     * <p>And there is always an answer. The statement was read off a value at a position of the
     * input, and the reading of the input holds every position a condition names — under every
     * case, where the name is one the cases of a sum share — so a position it holds no place for
     * is the reading contradicting what it read, and is said as that.
     */
    static DeclaredInput.Taking taking(TermPath position, CasesLeft cases, InputReading read) {
        InputDomain inputs = read.domain();
        DeclaredInput declared = inputs.declared(read.rules());
        DeclaredInput.Taking taking = taking(inputs, declared, position,
                declared.matchedAs(inputs.typeAt(position, read.rules()), cases), cases);
        if (taking == null) {
            throw new IllegalStateException("a statement of which case the value at `" + position
                    + "` is was read, and the reading of the input holds no place there");
        }
        return taking;
    }

    /** These conditions, with the rule stated at {@code states} reached under {@code assumed}. */
    static final class Collected {

        private final Map<ALine, List<OnTheWay>> byLine = new LinkedHashMap<>();
        private final Map<ALine, SaidOnTheWay> saidByLine = new LinkedHashMap<>();
        private final Map<ModelOccurrence, List<ConditionOnTheWay>> byOutcome =
                new LinkedHashMap<>();
        private final Map<ModelOccurrence, ConditionOnTheWay> byFork = new LinkedHashMap<>();

        /**
         * The truth or the comparison the construct {@code answers} answers, met as {@code met}
         * says.
         *
         * <p>Every copy of it, each as it was met. A comparison in a closure applied twice, or in a
         * value two regions build, is one construct the tree holds a copy of for each, and a run
         * is seen coming out of it through whichever copy it went through. So each copy is a way
         * of bringing it out, under what stood on the way to that copy, and none of them is what
         * every run past it met.
         */
        void answered(ModelOccurrence answers, ConditionOnTheWay met) {
            // Kept as met, and not in a set: what is filed here is every comparison of every
            // fork's condition, and a set would hash each deep account of its way to file it.
            byOutcome.computeIfAbsent(answers, _ -> new ArrayList<>()).add(met);
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
         *
         * <p>The readings a border is drawn in, which are known once the line is narrowed by what
         * arrives at it, and are what {@link #wayTo} is asked by.
         *
         * <p>Each case with what it put on the way and who put each of those there, and not those
         * of every case told together. One thing may be put on the ways to two cases by two
         * copies, and told together it would be filed under both copies for both cases — a line
         * told of a call a row at it never goes through.
         *
         * @param said who put each entry of {@code assumed} there
         */
        void reached(ModelOccurrence states, List<OnTheWay> assumed,
                     Map<WhereAPartDecides, Stating> whereEachDecides,
                     SaidOnTheWay said) {
            // And who put each entry there, beside the entries: every way that reaches the line
            // is one a row may come by, so what each says put an entry on it is said of the line.
            saidByLine.merge(new ALine(states, Optional.empty()), said, SaidOnTheWay::and);
            // A comparison inside a non-recursive helper is read once per call of it and each of
            // those calls is a construct of its own. A comparison inside a closure is the one the
            // author wrote, met through each copy an application of the closure makes. A run
            // reaches the rule through any of them, so what a row owes is what every way here
            // states — kept by neither alone, which would owe a row the conditions of a copy it
            // does not go through.
            byLine.merge(new ALine(states, Optional.empty()), List.copyOf(assumed),
                    Collected::commonTo);
            whereEachDecides.forEach((part, decides) -> {
                List<OnTheWay> way = new ArrayList<>(assumed);
                way.addAll(decides.entries());
                byLine.merge(new ALine(states, Optional.of(part)), List.copyOf(way),
                        Collected::commonTo);
                saidByLine.merge(new ALine(states, Optional.of(part)), said.and(decides.by()),
                        SaidOnTheWay::and);
            });
        }

        /**
         * What a row owes whichever of two ways it reaches one rule by: what both state, and a
         * decline from either — a condition one way could not take in is one the account cannot say
         * it took in, so it stays.
         */
        private static List<OnTheWay> commonTo(List<OnTheWay> one, List<OnTheWay> other) {
            List<OnTheWay> common = new ArrayList<>(one);
            common.retainAll(other);
            for (OnTheWay each : List.of(one, other).stream().flatMap(List::stream).toList()) {
                if (each instanceof OnTheWay.Declined && !common.contains(each)) {
                    common.add(each);
                }
            }
            return List.copyOf(common);
        }

        ReachingCuts made() {
            return new ReachingCuts(Lookup.built(put -> byLine.forEach(put::put)),
                    Lookup.built(put -> saidByLine.forEach(put::put)),
                    Lookup.built(put -> byOutcome.forEach((at, copies) ->
                            put.put(at, List.copyOf(copies)))),
                    Lookup.built(put -> byFork.forEach(put::put)));
        }
    }
}
