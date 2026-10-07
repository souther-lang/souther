package souther.compiler.partition;

import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;

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
                    way.narrowing(declarations), required, truths, way.takenIn());
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
        return new Reaching(declarations, Requirements.NONE, TruthsAsked.NONE, List.of());
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
     */
    record Reaching(SearchRegion region, Requirements requirements, TruthsAsked truths,
                    List<OnTheWay.TakenIn> boundedOnTheWay) implements Reachability {

        public Reaching {
            if (region == null || requirements == null || truths == null) {
                throw new IllegalArgumentException(
                        "a way a row reaches leaves it somewhere and asks something of it");
            }
            boundedOnTheWay = List.copyOf(boundedOnTheWay);
        }
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
