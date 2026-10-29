package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

/**
 * What a row has to be for a search to reach one border, in the words a composer works in.
 *
 * <p>{@link WayToTheBorder} is the account of the walk and this is what a composer may act on. The
 * two are one value read twice and never two values kept in step: this is derived from that
 * wherever somebody needs it, and nothing puts a condition here that is not on the account.
 *
 * <p><b>Every vocabulary, and none stands in for another.</b> A region says which numbers a
 * position may hold and has no word for which case a value turned out to be; a requirement says
 * which case and orders nothing; and a truth says which of a {@code Bool}'s two values stands at a
 * position, which is neither a number nor a case. Handed only the first, a composer wrote rows in
 * whichever arm the values happened to fall in; handed only the second, it wrote rows a guard above
 * turned back. The row is one row and what it has to be is one value, so every composer is handed
 * all of them here and none works one of them out from the way for itself.
 *
 * <p><b>Of the whole row and not of the positions an item names.</b> Where the item asks a position
 * to stand is what a search solves for; what this says of the same row holds of every position of
 * it, the solved-for ones included. Read as though the two were about different halves of a row, a
 * search fixed one position against the way and filled the rest against the declarations — which is
 * how a row came to carry a line's value and reach nothing.
 *
 * <p>Nothing here says a row that meets it arrives. A condition the walk could not state narrows
 * nothing here, so what this admits holds every row that reaches the border and may hold rows that
 * do not — the inclusion {@link SearchRegion} promises, kept whole once the second vocabulary is
 * beside it.
 *
 * <p><b>What was declined is not carried here.</b> It travels with the answer, on the
 * {@link WayToTheBorder} an outcome of a search keeps, and a composer does nothing with it: what a
 * row is composed against is what could be stated, and a copy of the rest sitting in the composer's
 * input would be a second list of one thing with nobody reading it.
 */
public sealed interface Reachability {

    /**
     * The way as a composer reads it, or the fact that nothing takes it.
     *
     * @param declarations what the declarations leave, which the way narrows
     */
    static Reachability of(WayToTheBorder way, SearchRegion declarations) {
        Reachability taken = taking(way, declarations, Ways.ONE);
        if (!(taken instanceof Reaching whole)) {
            return taken;
        }
        // Whether the conditions on the way hold together is the walk's to say, on a way with
        // nothing of several ways on it as much as on one with: a count asked twice, or a case a
        // relation's term needs, closes a way as a case asked twice does. Where a condition came
        // out one of several ways, a row is past it along one of them, and where every way of
        // some of them closes, nothing reaches.
        return switch (way.along()) {
            case OneOfEach.Walked.Closed<OnTheWay, Reachability>(var _, var why) -> why;
            case OneOfEach.Walked.Stopped<OnTheWay, Reachability>(var figure) ->
                    whole.splitAs(new Ways.Whole(way.severalWays(), figure, List.of(),
                            new ReadFrom(way, declarations)));
            case OneOfEach.Walked.Open<OnTheWay, Reachability> _
                    when way.severalWays().isEmpty() -> whole;
            case OneOfEach.Walked.Open<OnTheWay, Reachability>(var ways, var stoppedBy) -> {
                List<Reaching> along = new ArrayList<>();
                for (OneOfEach.Way<OnTheWay> one : ways) {
                    along.add(switch (one) {
                        case OneOfEach.Way.Chosen<OnTheWay>(var entries, var _) ->
                                reaching(new WayToTheBorder(entries), declarations);
                        // A condition the walk left as it stands is one this way was not split
                        // at past the figure, and is said as one, so that a row composed along
                        // it is not taken to have met it.
                        case OneOfEach.Way.LeftUnchosen<OnTheWay>(var chosen, var unchosen) ->
                                reaching(new WayToTheBorder(chosen), declarations).splitAs(
                                        new Ways.Whole(unchosen, stoppedBy, List.of(),
                                                new ReadFrom(new WayToTheBorder(Stream.concat(
                                                        chosen.stream(), unchosen.stream())
                                                        .toList()), declarations)));
                    });
                }
                // Every way a row takes is among them, so a search looking along each looks
                // along every row past the way, and what all of them state the way states.
                // Otherwise they are looked along first, each narrower than the way, and past
                // them the way is looked along whole — which every row past it is on, so none of
                // them being closed proves nothing — and the conditions it was not looked along
                // each way of say so.
                yield whole.splitAs(stoppedBy == null ? new Ways.Each(along)
                        : new Ways.Whole(way.severalWays(), stoppedBy, along,
                                new ReadFrom(way, declarations)));
            }
        };
    }

    /** {@code way} with what a run to the border got past working out
     *  ({@link Reaching#gettingPast}) taken in, where it is a way a row reaches. */
    static Reachability gettingPast(Reachability way, DemandReading.Answered answered) {
        return way instanceof Reaching reaching ? reaching.gettingPast(answered) : way;
    }

    /** {@code way}, one the walk found holds together, as a composer reads it. */
    private static Reaching reaching(WayToTheBorder way, SearchRegion declarations) {
        if (taking(way, declarations, Ways.ONE) instanceof Reaching open) {
            return open;
        }
        throw new IllegalStateException("a way the walk found open asks nothing twice, since the"
                + " walk asks of it all that is asked here");
    }

    /** {@code way} read in its own vocabularies, split as {@code ways} says. */
    private static Reachability taking(WayToTheBorder way, SearchRegion declarations, Ways ways) {
        Optional<OnTheWay.Settled> never = way.neverComesOut();
        if (never.isPresent()) {
            return new NothingComesOutThatWay(never.get());
        }
        Requirements required;
        switch (way.requirements()) {
            case Requirements.Merge.Merged(var both) -> required = both;
            case Requirements.Merge.Conflict conflict -> {
                return new NothingReaches(new TwoAtOnce.Cases(conflict));
            }
        }
        return switch (way.truths()) {
            case TruthsAsked.Merge.Merged(var truths) -> new Reaching(
                    way.narrowing(declarations), required, truths, way.takenIn(), ways,
                    way.declined(), Optional.of(way.takenIntoTheRegion()));
            case TruthsAsked.Merge.Conflict(var at) -> new NothingReaches(new TwoAtOnce.Truths(at));
        };
    }

    /**
     * Nothing stood on the way, so a row for the border is whatever the declarations leave.
     *
     * <p>{@link WayToTheBorder#UNTOUCHED} read here, and written out rather than sent through
     * {@link #of}: an account with nothing on it narrows nothing and asks nothing, so there is one
     * answer and no arm for the other one to arrive by.
     */
    static Reaching untouched(SearchRegion declarations) {
        return new Reaching(declarations, Requirements.NONE, TruthsAsked.NONE, List.of(),
                Ways.ONE, List.of(), Optional.of(List.of()));
    }

    /**
     * Whether a way is looked along as each of the ways a condition of several ways on it splits
     * it into ({@link OnTheWay#alternatives}).
     *
     * <p>Three answers and not a list that is sometimes empty. A way not split because nothing on
     * it came out one of several ways, and one not split because they were more than are looked
     * along, are looked for the same way and are not the same news: along each, a row is composed
     * against more than along the whole, so the second may be missing a row the first would have.
     */
    sealed interface Ways {

        /** Not split, and nothing in it to split at: no condition on it came out one of several
         *  ways. */
        Ways ONE = new One();

        /** What a search looks along: each way this is split into, or none past this one. */
        default List<Reaching> along() {
            return List.of();
        }

        /** Not split, and nothing in it to split at. */
        record One() implements Ways {}

        /**
         * Split into every way some row may take, each narrower than the way whole: every
         * combination of one open alternative of each condition of several ways
         * ({@link OneOfEach}). A way the rules leave nothing along is not among them, so one alone
         * is left where the rules close every other.
         *
         * <p>Every row past the way is along one of them, so what every one of them states is what
         * the way states, and what one states is no more than one way's. Where the figure left
         * some combination out, the way is not this but {@link Whole}.
         *
         * @param along one or more
         */
        record Each(List<Reaching> along) implements Ways {

            public Each {
                along = List.copyOf(along);
                if (along.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a way split is split into the ways some row may take, and has one");
                }
            }
        }

        /**
         * Not split whole, though {@code unsplit} came out one of several ways: the ways they split
         * it into are more than {@code figure} lets this look along or look for, so the first of
         * them are looked along and past them it is looked along whole.
         *
         * <p>The ones looked along are each enough for a row, and any of them may be the one an
         * author wrote the condition for, so they are not given up for the rest. The way whole is
         * still looked along past them, and only it says nothing reaches, since a row may be on a
         * way not among them.
         *
         * @param unsplit the conditions of several ways on it, in the order the walk met them
         * @param along   the ways the figure let through that some row may take, looked along
         *                before the way whole; none where every one of them was closed
         * @param from    what the way was read from, which a reader asking about some of its
         *                places reads again with each choice as it shows it comes to for them
         */
        record Whole(List<OnTheWay> unsplit, CompositionBudget figure, List<Reaching> along,
                     ReadFrom from)
                implements Ways {

            public Whole {
                unsplit = List.copyOf(unsplit);
                along = List.copyOf(along);
                if (unsplit.isEmpty() || figure == null || from == null
                        || !unsplit.stream().allMatch(OnTheWay::splitsTheWay)) {
                    throw new IllegalArgumentException("a way looked along whole past a figure has"
                            + " a condition of several ways on it, a figure it met, and an account"
                            + " it was read from");
                }
            }

            /**
             * Whether some condition it was not split at is one a row is composed against whole
             * along it — a statement the elements of one container meet together
             * ({@link RealizationTarget.ElementsMeetingTogether}) — so that along the way whole a
             * row meets more of it than along any one way the figure let through.
             *
             * @param behavior the behavior whose input the way reads
             */
            public boolean composedAgainstWhole(String behavior) {
                return unsplit.stream().anyMatch(each ->
                        RealizationTarget.ElementsMeetingTogether.of(behavior, each).isPresent());
            }
        }
    }

    /**
     * The account a way looked along whole was read from, and what the declarations left before
     * it.
     *
     * <p>Kept so that a reader concluding something of some places only reads the way again with
     * each choice as it shows it comes to for those places, and reads it the one way every way is
     * read ({@link #of}) rather than working out the ways of what it put together itself.
     */
    record ReadFrom(WayToTheBorder way, SearchRegion declarations) {

        public ReadFrom {
            if (way == null || declarations == null) {
                throw new IllegalArgumentException("a way is read from an account, over what the"
                        + " declarations leave");
            }
        }

        /** {@code onTheWay}, conditions some of which are this way's, read over the same
         *  declarations. */
        public Reachability readAs(List<OnTheWay> onTheWay) {
            return Reachability.of(new WayToTheBorder(onTheWay), declarations);
        }
    }

    /**
     * Where a row for the border may be written, and what it has to be to get there.
     *
     * @param truths          which value each {@code Bool} position the way read is to hold — the
     *                        third vocabulary, which every composer writes the way it writes a
     *                        case it is required to be, and none works out from the way itself
     * @param boundedOnTheWay what the walk asked of a row on the way, which a composer has to
     *                        compose a row to meet rather than read off {@code region}: some of it
     *                        narrowed the region and some of it, what every element meets, did not.
     *                        The demands and not the positions read off them: a demand over two
     *                        positions is one statement about the pair, and a composer holding a
     *                        bag of positions has no way to tell which of them it may settle apart
     *                        from the others
     * @param ways            where a condition on the way came out one of several ways, whether it
     *                        is split into each way some row may take ({@link Ways})
     * @param declined        what the way states that none of the above holds: a row past it is
     *                        held to more than {@code region} says, and where the values of two
     *                        positions lie against one another is not all it says
     * @param narrowedBy      what the declarations were narrowed by to make {@code region}, in
     *                        order ({@link WayToTheBorder#takenIntoTheRegion}) — or empty where the
     *                        region was made some other way. Two ways of one reading narrowed by
     *                        the same are over one region, which the region's own value does not
     *                        say
     * @param gotPast         what the run to the border got past working out narrowed the region
     *                        by, which no condition of the way states
     * @param tied            the places that run ties together, or may stop on where nothing says
     *                        when, which a region does not say
     * @param unsaid          whether that run may stop on something no place names, so that no
     *                        number is known free of what it works out
     * @param owed            the operators that run may stop at whose owner says where they
     *                        answer, each owed a proof some run gets past it
     *                        ({@link DemandReading.Answered#owed})
     * @param before          what the applications of a closure before the one the border is
     *                        reached in work out ({@link DemandReading.Answered#before})
     */
    record Reaching(SearchRegion region, Requirements requirements, TruthsAsked truths,
                    List<OnTheWay.TakenIn> boundedOnTheWay, Ways ways,
                    List<OnTheWay.Declined> declined,
                    Optional<List<TakenConstraint>> narrowedBy,
                    List<TakenConstraint> gotPast, List<DemandReading.Tie> tied, boolean unsaid,
                    List<Pullback.StopObligation> owed,
                    List<DemandReading.PriorApplications> before)
            implements Reachability {

        public Reaching {
            if (region == null || requirements == null || truths == null || ways == null
                    || declined == null || narrowedBy == null || gotPast == null
                    || tied == null || owed == null || before == null) {
                throw new IllegalArgumentException(
                        "a way a row reaches leaves it somewhere and asks something of it");
            }
            boundedOnTheWay = List.copyOf(boundedOnTheWay);
            declined = List.copyOf(declined);
            narrowedBy = narrowedBy.map(List::copyOf);
            gotPast = List.copyOf(gotPast);
            tied = List.copyOf(tied);
            owed = List.copyOf(owed);
            before = List.copyOf(before);
        }

        /** A way a run has got past nothing on that a region says or that ties places. */
        public Reaching(SearchRegion region, Requirements requirements, TruthsAsked truths,
                        List<OnTheWay.TakenIn> boundedOnTheWay, Ways ways,
                        List<OnTheWay.Declined> declined,
                        Optional<List<TakenConstraint>> narrowedBy) {
            this(region, requirements, truths, boundedOnTheWay, ways, declined, narrowedBy,
                    List.of(), List.of(), false, List.of(), List.of());
        }

        /** The ways this is split into, each narrower than this one; none where it is not
         *  split. */
        public List<Reaching> along() {
            return ways.along();
        }

        /**
         * The ways a row is composed along to witness this one, in the order they are tried: each
         * way this is split into, looked at the same way, and this whole where the split is not
         * every way a row may take, which includes where it is none.
         *
         * <p>Not {@link #along()}, which a walk that follows the split reads and which is empty
         * for a way that is not split. A search that asks this of each way it tries would ask the
         * way itself again; it asks it of the way it was given.
         */
        public List<Reaching> waysToTryForARow() {
            return switch (ways) {
                case Ways.One _ -> List.of(this);
                case Ways.Each each -> each.along().stream()
                        .flatMap(way -> way.waysToTryForARow().stream())
                        .toList();
                case Ways.Whole whole -> Stream.concat(
                        whole.along().stream().flatMap(way -> way.waysToTryForARow().stream()),
                        Stream.of(this)).toList();
            };
        }

        /**
         * Regions that between them hold every row past this way: the region of each way it is
         * split into, where it is split into every way a row may take, and its own region
         * otherwise.
         *
         * <p>What a question about the rows that arrive somewhere is asked of. The region alone
         * spans every way, so a choice between runs of one number leaves the values between the
         * runs in it: a line drawn there looks reached when no way a row takes gets to it, and a
         * value there stands beside a line as if a row held it. Past a figure
         * the ways looked along are not every way, so only the region whole is a statement about
         * every row.
         */
        public List<SearchRegion> holdingEveryRow() {
            return switch (ways) {
                case Ways.Each each -> each.along().stream().map(Reaching::region).toList();
                case Ways.One _, Ways.Whole _ -> List.of(region);
            };
        }

        /** The same way, split as {@code split} says. What the way asks of a row is the same
         *  however it is split, so it is not worked out again. */
        Reaching splitAs(Ways split) {
            return new Reaching(region, requirements, truths, boundedOnTheWay, split, declined,
                    narrowedBy, gotPast, tied, unsaid, owed, before);
        }

        /** Whether every row of {@code region} meets {@code each}, shown by no row meeting its
         *  denial; a condition of a shape that has none is not shown to be met. */
        private static boolean heldAtEveryRow(TakenConstraint each, SearchRegion before,
                                              SearchRegion region) {
            return each instanceof TakenConstraint.Affine(var form, var rel)
                    && (TakenConstraint.holdsOverTheRunsOf(form, rel, before)
                            || TakenConstraint.nothingMeetsAll(
                                    List.of(new TakenConstraint.Affine(form, rel.denied())),
                                    region));
        }

        /** Whether taking {@code each} in moves where a number it names runs or what is held
         *  apart from it, going from {@code before} to {@code after}. */
        private static boolean movesAny(TakenConstraint each, SearchRegion before,
                                        SearchRegion after) {
            for (NumericTerm term : each.terms()) {
                if (term instanceof NumericTerm.FromOnePosition one
                        && (!Objects.equals(after.wholeRunOf(one), before.wholeRunOf(one))
                                || !after.apartAt(one).equals(before.apartAt(one)))) {
                    return true;
                }
            }
            return false;
        }

        /**
         * This with {@code these}, what the run to the border got past working out, taken into the
         * region of it and of each way it is split into. A way they leave no input is kept as it
         * is, with what they tie and what they leave unsaid: the walk proves that no row arrives
         * there, from the same operators, and says so; a region narrowed to nothing here would
         * be one more reader's account of it.
         */
        Reaching gettingPast(DemandReading.Answered answered) {
            if (answered.equals(DemandReading.Answered.NOTHING)) {
                return this;
            }
            List<DemandReading.Tie> ties = new ArrayList<>(tied);
            ties.addAll(answered.tied());
            // Only what narrows: a bound the region already holds is nothing a reader of this
            // way is to be told of.
            List<TakenConstraint> narrowing = new ArrayList<>();
            SearchRegion narrowed = region;
            for (TakenConstraint each : answered.narrowing()) {
                SearchRegion next = each.narrowing(narrowed);
                // One number that no run of moves is one the region already holds. Several say
                // how they go together, which no run of one of them shows: a sum held below a
                // greatest value leaves each its values and the pair fewer. Unless every row of
                // the region meets it, which leaves them as they are.
                boolean keeps = each.terms().size() > 1
                        ? !heldAtEveryRow(each, region, narrowed) : movesAny(each, narrowed, next);
                if (keeps) {
                    narrowing.add(each);
                    narrowed = next;
                }
            }
            Optional<List<TakenConstraint>> by = narrowedBy.map(was -> {
                List<TakenConstraint> both = new ArrayList<>(was);
                both.addAll(narrowing);
                return both;
            });
            Ways split = switch (ways) {
                case Ways.One one -> one;
                case Ways.Each each -> new Ways.Each(each.along().stream()
                        .map(one -> one.gettingPast(answered)).toList());
                // Read again from the declarations narrowed by what the run got past, so that a
                // reader reading the way again is as narrow as this one.
                case Ways.Whole whole -> new Ways.Whole(whole.unsplit(), whole.figure(),
                        whole.along().stream().map(one -> one.gettingPast(answered)).toList(),
                        new ReadFrom(whole.from().way(),
                                TakenConstraint.narrowedBy(narrowing,
                                        whole.from().declarations())));
            };
            boolean unsaidNow = unsaid || answered.unsaid();
            List<Pullback.StopObligation> owedNow = new ArrayList<>(owed);
            owedNow.addAll(answered.owed());
            List<DemandReading.PriorApplications> beforeNow = new ArrayList<>(before);
            beforeNow.addAll(answered.before());
            // A region nothing moved is the one the way already had, which is asked nothing again.
            if (!narrowing.isEmpty() && narrowed.emptiness().isPresent()) {
                return new Reaching(region, requirements, truths, boundedOnTheWay, split,
                        declined, narrowedBy, gotPast, ties, unsaidNow, owedNow, beforeNow);
            }
            List<TakenConstraint> past = new ArrayList<>(gotPast);
            past.addAll(narrowing);
            return new Reaching(narrowed, requirements, truths, boundedOnTheWay, split, declined,
                    by, past, ties, unsaidNow, owedNow, beforeNow);
        }

        /**
         * The cases this takes a row through, with the ones each of {@code items} is written
         * under — or the first item written under a case this does not take.
         *
         * <p>A row is one value, so what the way says and where an item's numbers are written are
         * one set of cases. A line read at a name the cases of a sum share is read under each case,
         * and the way to it may take a row through only some of them — or, split at the cases a
         * narrowing leaves, through one of them along each way. Asked before anything is composed
         * for the item, so that a reading off the way is the model's answer about it and not a
         * search that tried values and came to nothing.
         */
        public Written writing(Collection<? extends RealizationTarget> items) {
            Requirements required = requirements;
            for (RealizationTarget each : items) {
                if (!(required.merge(each.writeRoot().requirements())
                        instanceof Requirements.Merge.Merged(Requirements both))) {
                    return new Written.OffTheWay(each);
                }
                required = both;
            }
            return new Written.Under(required);
        }
    }

    /** Where an item is written, against the cases a way takes a row through
     *  ({@link Reaching#writing}). */
    sealed interface Written {

        /** Every item is written under a case the way takes, and these are the cases together. */
        record Under(Requirements required) implements Written {}

        /** {@code item} is written under a case the way does not take. */
        record OffTheWay(RealizationTarget item) implements Written {}
    }

    /**
     * The way asks one position to be two things at once, so no row takes it.
     *
     * <p>A fact about the model rather than a search that came up short. Two arms of two forks on
     * one position are reached by no value, and a search told to compose against the two of them
     * would report every candidate refused — which reads as a model that admits nothing where what
     * happened is that nothing arrives here at all.
     */
    record NothingReaches(TwoAtOnce why) implements Reachability {

        public NothingReaches {
            if (why == null) {
                throw new IllegalArgumentException("a way nothing takes asks some position twice");
            }
        }
    }

    /**
     * The statements of numbers on the way weigh one form of terms alike and leave no point of the
     * line in common, so no row takes it.
     *
     * <p>A fact about the model like {@link NothingReaches}, and not that: no position is asked
     * twice. The terms may be read from several positions, and it is the relation between them
     * that the statements contradict, so there is no position to name. What proves it is the
     * statements, which this carries.
     *
     * @param statements the statements of the way, of which some one form is held to no point
     */
    record NumbersLeaveNone(List<TakenConstraint.Affine> statements) implements Reachability {

        public NumbersLeaveNone {
            if (statements == null || statements.isEmpty()) {
                throw new IllegalArgumentException("numbers that leave none are some statements");
            }
            statements = List.copyOf(statements);
        }
    }

    /**
     * Which position a way asks to be two things, in the vocabulary it asked them in.
     *
     * <p>Two, because a position is asked two ways: to be a case, and to hold one of the two values
     * a {@code Bool} has. Both are the one fact {@link NothingReaches} says, and each says which
     * position.
     */
    sealed interface TwoAtOnce {

        /** The position asked twice. */
        TermPath at();

        /** Two cases of it that leave no case in common. */
        record Cases(Requirements.Merge.Conflict conflict) implements TwoAtOnce {

            public Cases {
                if (conflict == null) {
                    throw new IllegalArgumentException("two cases of some position");
                }
            }

            @Override
            public TermPath at() {
                return conflict.at();
            }
        }

        /** Both values of a {@code Bool}. */
        record Truths(TermPath at) implements TwoAtOnce {

            public Truths {
                if (at == null) {
                    throw new IllegalArgumentException("both values of some position");
                }
            }
        }

        /**
         * How many elements of the container at {@code at} meet a statement, asked to be in two
         * regions that leave it no count in common: some element meeting it and none, or two
         * counts apart.
         */
        record Counts(TermPath at) implements TwoAtOnce {

            public Counts {
                if (at == null) {
                    throw new IllegalArgumentException("two counts of the elements of some"
                            + " container");
                }
            }
        }
    }

    /**
     * A condition on the way comes out the other way for every row, so no row takes it.
     *
     * <p>The same kind of fact as the one above and not a search that came up short: what settles
     * it is what the source wrote — a predicate that always holds, sides whose difference is the
     * same on every row — and a search composing against it would report every candidate refused
     * for a way nothing arrives at.
     */
    record NothingComesOutThatWay(OnTheWay.Settled condition) implements Reachability {

        public NothingComesOutThatWay {
            if (condition == null || condition.thisWay()) {
                throw new IllegalArgumentException(
                        "a way no row takes is closed by a condition no row brings out that way: "
                                + condition);
            }
        }
    }
}
