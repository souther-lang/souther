package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Optional;

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
                    whole.splitAs(new Ways.Whole(way.severalWays(), figure, List.of()));
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
                                        new Ways.Whole(unchosen, stoppedBy, List.of()));
                    });
                }
                // Every way a row takes is among them, so a search looking along each looks
                // along every row past the way, and what all of them state the way states.
                // Otherwise they are looked along first, each narrower than the way, and past
                // them the way is looked along whole — which every row past it is on, so none of
                // them being closed proves nothing — and the conditions it was not looked along
                // each way of say so.
                yield whole.splitAs(stoppedBy == null ? new Ways.Each(along)
                        : new Ways.Whole(way.severalWays(), stoppedBy, along));
            }
        };
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
         */
        record Whole(List<OnTheWay> unsplit, CompositionBudget figure, List<Reaching> along)
                implements Ways {

            public Whole {
                unsplit = List.copyOf(unsplit);
                along = List.copyOf(along);
                if (unsplit.isEmpty() || figure == null
                        || !unsplit.stream().allMatch(OnTheWay::splitsTheWay)) {
                    throw new IllegalArgumentException("a way looked along whole past a figure has"
                            + " a condition of several ways on it, and a figure it met");
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
     */
    record Reaching(SearchRegion region, Requirements requirements, TruthsAsked truths,
                    List<OnTheWay.TakenIn> boundedOnTheWay, Ways ways,
                    List<OnTheWay.Declined> declined,
                    Optional<List<TakenConstraint>> narrowedBy)
            implements Reachability {

        public Reaching {
            if (region == null || requirements == null || truths == null || ways == null
                    || declined == null || narrowedBy == null) {
                throw new IllegalArgumentException(
                        "a way a row reaches leaves it somewhere and asks something of it");
            }
            boundedOnTheWay = List.copyOf(boundedOnTheWay);
            declined = List.copyOf(declined);
            narrowedBy = narrowedBy.map(List::copyOf);
        }

        /** The ways this is split into, each narrower than this one; none where it is not
         *  split. */
        public List<Reaching> along() {
            return ways.along();
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
                    narrowedBy);
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
