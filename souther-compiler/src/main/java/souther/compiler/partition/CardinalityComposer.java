package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Containers with so many of their elements meeting each of some statements.
 *
 * <p>What a count asks of a row is elements, and whether an element meets a statement turns on the
 * element's own number and on whatever else the statement reads. The numbers beside an element are
 * fixed before this is asked, as numbers of the row; this chooses elements against them.
 *
 * <p><b>Elements by what they answer.</b> Where each relation over the element turns over is worked
 * out once ({@link AStatementAtARow#turnsAt}). Between two of those places, and at each of them,
 * every relation reads any value the same way, so a value from each is every way an element can
 * answer them. Each value is read for every statement on the container at once, the way a row's
 * element is read, and the values are grouped by what they answer: one group for each way of
 * answering all the statements together. A value a statement could not be read at is neither
 * counted for it nor against it. It goes in no group, and what kept it out is said.
 *
 * <p><b>Then how many of each.</b> A container of so many elements is so many from each group, and
 * it meets every count where the elements of the groups that meet each statement are as many as
 * that count asks. The sizes are walked from none up, and each way of sharing a size out among the
 * groups that meets every count is a container.
 *
 * <p>A list holds one value as often as it likes. A set holds each value once, so a group is drawn
 * on for as many different values as it is asked for, and where it has too few that sharing builds
 * nothing. Which is no proof that no container meets the counts: the values of a group are the
 * ones this named, and a run holds others.
 *
 * <p>Every container is read again as a whole before it is offered. What the groups promise is what
 * each value answered alone, and reading the container is what a row's reading does.
 */
final class CardinalityComposer {

    private static final int MOST_ELEMENTS =
            CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH.maximum();

    private static final int MOST_OFFERED =
            CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED.maximum();

    private static final int MOST_SHARES =
            CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT.maximum();

    /**
     * Containers of {@code sourceType} meeting every one of {@code counts} at the set {@code
     * demands} asks it for, with some element standing in the set asked of each of {@code
     * standingAt}, and holding as many elements as {@code manyItHolds} is asked for where it is not
     * null.
     *
     * @param standingAt the element itself, each asked to stand in a set: a value the row places at
     *                   an element, which some element of the container is
     * @param within     the region with every number of the row a count's statement reads beside
     *                   an element standing at one value
     */
    static TermRealizations.Realization compose(Type sourceType,
                                                List<RealizationTarget.ACount> counts,
                                                SequencedMap<RealizationTarget, AskedAt> demands,
                                                RealizationTarget.OfANumber manyItHolds,
                                                List<RealizationTarget.OfANumber> standingAt,
                                                SearchRegion within,
                                                RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        TermPath container = counts.getFirst().count().container();
        List<Asked> asked = new ArrayList<>();
        // Each count as the counts it is asked for, and not as the one a row was named at: the
        // item and every condition on the way that ask for it leave a region, and which count of
        // it the container holds is chosen here.
        for (RealizationTarget.ACount each : counts) {
            AskedAt at = demands.get(each);
            if (at == null) {
                return none("nothing says how many elements of `" + container + "` are to meet `"
                        + each + "`");
            }
            asked.add(new Asked.SoManyMeeting(each.count().perElement(), at.about().values()));
        }
        NumericSet size = null;
        if (manyItHolds != null) {
            AskedAt holds = demands.get(manyItHolds);
            if (holds == null || holds.walking() == null) {
                return none("nothing says how many elements `" + container + "` holds");
            }
            size = holds.walking();
        }
        TypeView view = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        if (!(view.shape() instanceof Shape.Sequence holding)
                || !container.element().outermostContainer().equals(container)) {
            return notChosen("`" + container + "` is no list or set written where it stands");
        }
        Element element = Element.of(counts, container);
        if (element == null) {
            return notChosen("an element of `" + container + "` is not one number the statements"
                    + " read");
        }
        for (RealizationTarget.OfANumber each : standingAt) {
            AskedAt at = demands.get(each);
            if (at == null || at.walking() == null) {
                return none("nothing says where an element of `" + container + "` is to stand");
            }
            asked.add(new Asked.SomeElementIn(at.walking(), element.carrier()));
        }
        // The numbers beside an element, each at the one value the row was fixed at.
        Map<NumericTerm, Place> beside = new LinkedHashMap<>();
        Map<TermPath, ObservedValue> written = new LinkedHashMap<>();
        for (NumericTerm term : element.beside()) {
            Carrier on = element.on().get(term);
            Place at = settled(within, term);
            if (on == null || at == null) {
                return none("`" + term + "` stands at no one value beside the elements of `"
                        + container + "`");
            }
            beside.put(term, at);
            written.put(term.subjectPath(), on.valueOf(at));
        }
        NumericDomain.Bounds run = switch (within.projectionOf(element.term())) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                    held == null ? NumericDomain.Bounds.OPEN : held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case null -> NumericDomain.Bounds.OPEN;
        };
        List<ExactRatio> turns = new ArrayList<>();
        for (Asked each : asked) {
            List<ExactRatio> where = each.turnsAt(element.term(), beside);
            if (where == null) {
                return notChosen("where `" + each + "` turns over an element of `" + container
                        + "` could not be worked out");
            }
            turns.addAll(where);
        }
        boolean distinct = holding.kind() == Shape.Sequence.Kind.SET;
        Set<CompositionCapacity> unheld = new LinkedHashSet<>();
        Groups groups = Groups.of(asked, container, element, written,
                run == null ? List.of() : valuesAlong(element.carrier(), run, turns,
                        distinct ? MOST_ELEMENTS : 1, unheld));
        TypeView ofTheElement = TypeView.of(holding.element(), ruleSource.inners(),
                ruleSource.symbols(), ruleSource.kinds(), ruleSource.sums());
        List<FixtureTemplate> built = new ArrayList<>();
        Set<CompositionBudget> refused = EnumSet.noneOf(CompositionBudget.class);
        Sharing sharing = new Sharing(groups, asked, size, distinct, MOST_SHARES);
        for (int elements = 0; ; elements++) {
            if (elements > MOST_ELEMENTS) {
                refused.add(CompositionBudget.ELEMENTS_A_COUNT_IS_COMPOSED_WITH);
                break;
            }
            // Each sharing is built as it is found, so what stops the walk is a container offered
            // or a sharing looked at, and never a list of them made first.
            boolean walkedThem = sharing.each(elements, share -> {
                if (built.size() == MOST_OFFERED) {
                    return false;
                }
                List<Place> values = groups.drawn(share, distinct);
                if (readsAsAsked(asked, container, element, written, values)) {
                    FixtureTemplate one = holdingThese(values, element.carrier(), view,
                            ofTheElement, ruleSource);
                    if (one != null) {
                        built.add(one);
                    }
                }
                return true;
            });
            // Stopped with a sharing in front of it: for the sharings this looks at, or else for the
            // containers it offers, which is the one other thing that turns a sharing away.
            if (!walkedThem) {
                refused.add(sharing.spent() ? CompositionBudget.SHARES_A_COUNT_IS_TRIED_AT
                        : CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED);
                break;
            }
        }
        CompositionShortfall rest = CompositionShortfall.of(refused,
                groups.unread().isEmpty() ? Set.of()
                        : Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT),
                unheld);
        if (!built.isEmpty()) {
            return new TermRealizations.Realization.Built(built, rest);
        }
        if (!rest.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(rest);
        }
        if (!rest.nothing()) {
            return new TermRealizations.Realization.Unexhausted(rest, groups.unreadSaid());
        }
        return none("no container of `" + container + "` this composed meets every count asked");
    }

    /**
     * One thing the elements of the container are asked, and how many of them are to answer it.
     *
     * <p>Two kinds, and one walk over both. How many elements meet a statement is a count; an
     * element standing at a value the row placed there is some element being one of a set. Both
     * are a question each value answers and a number of the elements that answer it, so a container
     * composed for both is composed by sharing elements out among what they answer together.
     */
    private sealed interface Asked {

        /** Whether {@code value}, as the element {@code row} reads, answers this. */
        AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row);

        /** Whether a container with {@code meeting} elements answering this has as many as this
         *  asks. */
        boolean asMany(int meeting);

        /** Where an element's answer to this turns over, with the numbers beside it where {@code
         *  beside} says; null where that could not be worked out. */
        List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside);

        /** Whether a container of {@code values}, read whole as {@code row}, has as many elements
         *  answering this as it asks — for every count the reading leaves, where one was not read. */
        AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                     BorderQuantity.Observation row);

        /** How many elements meet {@code perElement}: one of the counts {@code wanted} holds. */
        record SoManyMeeting(AStatementAtARow perElement, LevelRegion wanted) implements Asked {

            @Override
            public AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row) {
                return perElement.at(row);
            }

            /** Read the way the row's own reading reads the count. */
            @Override
            public AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                                BorderQuantity.Observation row) {
                AStatementAtARow.HowManyAtARow counted = perElement.howManyMeetIn(container, row);
                return counted == null
                        ? new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK))
                        : counted.whether(n -> ExactAnswer.held(asMany(n)));
            }

            @Override
            public boolean asMany(int meeting) {
                return wanted.contains(new Level.OfTheQuantity(ExactRatio.of(meeting)));
            }

            @Override
            public List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                return perElement.turnsAt(element, beside);
            }
        }

        /** Some element standing in {@code set}, on the order the element is written on. */
        record SomeElementIn(NumericSet set, Carrier on) implements Asked {

            @Override
            public AStatementAtARow.Answer at(Place value, BorderQuantity.Observation row) {
                return set.holds(value, on) ? AStatementAtARow.Answer.HOLDS
                        : AStatementAtARow.Answer.FAILS;
            }

            @Override
            public boolean asMany(int meeting) {
                return meeting >= 1;
            }

            @Override
            public AStatementAtARow.Answer over(TermPath container, List<Place> values,
                                                BorderQuantity.Observation row) {
                return values.stream().anyMatch(value -> set.holds(value, on))
                        ? AStatementAtARow.Answer.HOLDS : AStatementAtARow.Answer.FAILS;
            }

            /** The ends of the set, which are where standing in it turns over. */
            @Override
            public List<ExactRatio> turnsAt(NumericTerm element, Map<NumericTerm, Place> beside) {
                List<ExactRatio> out = new ArrayList<>();
                NumericDomain.Bounds extent = set.extent();
                for (Endpoint end : Arrays.asList(extent.min(), extent.max())) {
                    if (end != null) {
                        out.add(Count.number(end.at()).exactly());
                    }
                }
                return out;
            }
        }
    }

    /**
     * The number the statements read at each element, and the numbers they read beside it.
     *
     * @param term    the element's own number, which is the element itself
     * @param carrier the order the element is written on
     * @param beside  every number the statements read that stands at one place of the row, in the
     *                order they were met
     * @param on      the order each number the statements read is written on
     */
    private record Element(NumericTerm term, Carrier carrier, List<NumericTerm> beside,
                           Map<NumericTerm, Carrier> on) {

        /**
         * The element of {@code container} as every count reads it, or null where one of them
         * reads it as something other than one number standing at the element itself.
         *
         * <p>A number of another container's elements is not beside the element: it is read
         * element by element where the statement is asked, which is where it is left.
         */
        static Element of(List<RealizationTarget.ACount> counts, TermPath container) {
            NumericTerm own = null;
            Set<NumericTerm> beside = new LinkedHashSet<>();
            Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
            for (RealizationTarget.ACount each : counts) {
                on.putAll(each.count().on());
                for (NumericTerm term : each.count().numbers()) {
                    if (term.subjectPath().isAtOrUnder(container.element())) {
                        if (!(term instanceof NumericTerm.ValueOf)
                                || !term.subjectPath().equals(container.element())
                                || (own != null && !own.equals(term))) {
                            return null;
                        }
                        own = term;
                    } else if (!term.subjectPath().insideAContainer()) {
                        beside.add(term);
                    }
                }
            }
            Carrier carrier = own == null ? null : on.get(own);
            if (carrier == null || !carrier.counts()) {
                return null;
            }
            return new Element(own, carrier, List.copyOf(beside), on);
        }
    }

    /** The one place the region leaves {@code term} at, or null where it leaves more or none. */
    private static Place settled(SearchRegion within, NumericTerm term) {
        if (!(within.projectionOf(term)
                instanceof NumericDomain.FormProjection.Within(NumericDomain.Bounds held))
                || held == null || held.min() == null || held.max() == null
                || !held.min().inclusive() || !held.max().inclusive()
                || !held.min().at().sameAs(held.max().at())) {
            return null;
        }
        return held.min().at();
    }

    /**
     * Values of the element inside {@code run}: each place a relation turns at that is a value, and
     * up to {@code each} different values from every run between two of them and past the last.
     *
     * <p>Nearest the place a run is bounded by, which is the value beside the line an author would
     * write. A run bounded on neither side has one value taken, as a place with nothing to be near.
     *
     * <p>Where a relation turns is a number and not always a value: {@code 3 * x > 1} turns at a
     * third, which no element is. It parts the values either side of it all the same, so the runs
     * beside it are bounded there ({@link #partingAt}), and a place a value can be is a value
     * besides.
     */
    private static List<Place> valuesAlong(Carrier carrier, NumericDomain.Bounds run,
                                           List<ExactRatio> turns, int each,
                                           Set<CompositionCapacity> unheld) {
        List<ExactRatio> at = turns.stream().distinct().sorted().toList();
        List<Parting.Parts> parted = new ArrayList<>();
        for (int i = 0; i < at.size(); i++) {
            switch (partingAt(at.get(i), i == 0 ? null : at.get(i - 1),
                    i == at.size() - 1 ? null : at.get(i + 1))) {
                case Parting.Parts parts -> parted.add(parts);
                // A place this could not part the values at leaves the runs beside it walked as
                // one, which is a number not held and is said.
                case Parting.NotWorkedOut(UnheldNumber why) -> unheld.add(new CompositionCapacity(
                        CompositionCapacity.Where.PLACES_AN_ELEMENT_TURNS_AT, why));
            }
        }
        List<Place> out = new ArrayList<>();
        Endpoint low = run.min();
        for (int i = 0; i <= parted.size(); i++) {
            Parting.Parts parting = i < parted.size() ? parted.get(i) : null;
            Endpoint high = parting == null ? run.max()
                    : tighter(run.max(), parting.below(), false);
            out.addAll(walked(carrier, low, high, each));
            if (parting != null) {
                Place itself = parting.itself();
                if (itself != null && carrier.onTheGrid(itself) != null && inside(run, itself)) {
                    out.add(carrier.onTheGrid(itself));
                }
                low = tighter(run.min(), parting.above(), true);
            }
        }
        return out;
    }

    /**
     * How a place a relation turns at parts the values beside it.
     *
     * <p>A place a value can be is that value, with the runs either side open there. A place none
     * can be — a third — is bounded on each side by the decimal nearest it there, at as many digits
     * as keep each bound clear of the places beside it ({@code below} and {@code above}), which is
     * worked out from how far away they are and not looked for.
     */
    sealed interface Parting {

        /**
         * The runs either side of the place, bounded there.
         *
         * @param below  the end of the run below the place
         * @param itself the place, where a value can stand there; null where none can
         * @param above  the end of the run above it
         */
        record Parts(Endpoint below, Place itself, Endpoint above) implements Parting {}

        /** The place could not be parted at, for this. */
        record NotWorkedOut(UnheldNumber why) implements Parting {}
    }

    /**
     * How the values beside {@code turn} are parted there, with the places a relation turns at
     * either side of it, where there are any.
     */
    static Parting partingAt(ExactRatio turn, ExactRatio below, ExactRatio above) {
        switch (Count.written(turn)) {
            case ExactAnswer.Held<Optional<Count>>(Optional<Count> written)
                    when written.isPresent() -> {
                Count itself = written.get();
                return new Parting.Parts(Endpoint.exclusive(itself), itself,
                        Endpoint.exclusive(itself));
            }
            case ExactAnswer.Held<Optional<Count>> _ -> { }
            case ExactAnswer.Unheld<Optional<Count>> notHeld -> {
                return new Parting.NotWorkedOut(notHeld.why());
            }
        }
        // Digits enough that one step of the last of them is less than the distance to either
        // place beside it: ten to the power of how many digits the reciprocal of that distance
        // has is more than the reciprocal.
        ExactAnswer<ExactRatio> nearest = ExactAnswer.held(ExactRatio.ONE);
        for (ExactRatio beside : Arrays.asList(below, above)) {
            if (beside != null) {
                ExactAnswer<ExactRatio> apart = turn.minus(beside).map(ExactRatio::abs);
                nearest = nearest.flatMap(sofar -> apart.map(gap ->
                        gap.compareTo(sofar) < 0 ? gap : sofar));
            }
        }
        if (!(nearest.flatMap(gap -> ExactRatio.ONE.dividedBy(gap)).flatMap(ExactRatio::ceiling)
                instanceof ExactAnswer.Held<BigInteger>(BigInteger reciprocal))) {
            return new Parting.NotWorkedOut(UnheldNumber.MORE_ROOM_COULD_ANSWER);
        }
        int digits = reciprocal.toString().length();
        ExactRatio scale = ExactRatio.of(BigInteger.TEN.pow(digits));
        ExactAnswer<ExactRatio> scaled = turn.times(scale);
        if (!(scaled.flatMap(ExactRatio::floor) instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger floor))
                || !(scaled.flatMap(ExactRatio::ceiling) instanceof ExactAnswer.Held<BigInteger>(
                        BigInteger ceiling))) {
            return new Parting.NotWorkedOut(UnheldNumber.MORE_ROOM_COULD_ANSWER);
        }
        return new Parting.Parts(
                Endpoint.inclusive(Count.of(new BigDecimal(floor, digits))), null,
                Endpoint.inclusive(Count.of(new BigDecimal(ceiling, digits))));
    }

    /** Up to {@code each} different values between two ends, from the end there is. */
    private static List<Place> walked(Carrier carrier, Endpoint low, Endpoint high, int each) {
        List<Place> out = new ArrayList<>();
        Towards from = low == null && high != null ? Towards.BELOW : Towards.ABOVE;
        Endpoint lo = low;
        Endpoint hi = high;
        while (out.size() < each && Endpoint.someValueLiesBetween(lo, hi)) {
            Place next = carrier.somethingInside(lo, hi, from);
            if (next == null || out.stream().anyMatch(next::sameAs)) {
                break;
            }
            out.add(next);
            if (from == Towards.ABOVE) {
                lo = Endpoint.exclusive(next);
            } else {
                hi = Endpoint.exclusive(next);
            }
        }
        return out;
    }

    /** Of two ends on one side, the one that leaves less; either may be missing. */
    private static Endpoint tighter(Endpoint one, Endpoint other, boolean lower) {
        if (one == null) {
            return other;
        }
        int compared = one.at().compareTo(other.at());
        if (compared == 0) {
            return one.inclusive() ? other : one;
        }
        return lower == compared > 0 ? one : other;
    }

    private static boolean inside(NumericDomain.Bounds run, Place at) {
        return (run.min() == null || run.min().at().compareTo(at) < 0
                        || (run.min().inclusive() && run.min().at().compareTo(at) == 0))
                && (run.max() == null || run.max().at().compareTo(at) > 0
                        || (run.max().inclusive() && run.max().at().compareTo(at) == 0));
    }

    /**
     * The values, grouped by what each answers of every statement, in the order they were named.
     *
     * @param answers each group's answer, one per count, true where the value meets the statement
     * @param values  each group's values
     * @param unread  what kept a value out of every group, where something did
     */
    private record Groups(List<boolean[]> answers, List<List<Place>> values,
                          Set<ReadingGap> unread) {

        static Groups of(List<Asked> asked, TermPath container,
                         Element element, Map<TermPath, ObservedValue> written,
                         List<Place> values) {
            Map<String, Integer> found = new LinkedHashMap<>();
            List<boolean[]> answers = new ArrayList<>();
            List<List<Place>> held = new ArrayList<>();
            Set<ReadingGap> unread = new LinkedHashSet<>();
            values:
            for (Place value : values) {
                AnElementRead read = new AnElementRead(container, element.term().subjectPath(),
                        written, List.of(element.carrier().valueOf(value)));
                BorderQuantity.Observation one = read.elements().getFirst();
                boolean[] answer = new boolean[asked.size()];
                for (int i = 0; i < asked.size(); i++) {
                    switch (asked.get(i).at(value, one)) {
                        case AStatementAtARow.Answer.Holds _ -> answer[i] = true;
                        case AStatementAtARow.Answer.Fails _ -> answer[i] = false;
                        case AStatementAtARow.Answer.CouldNotTell(var why) -> {
                            unread.addAll(why);
                            continue values;
                        }
                    }
                }
                String key = Arrays.toString(answer);
                Integer at = found.get(key);
                if (at == null) {
                    found.put(key, answers.size());
                    answers.add(answer);
                    held.add(new ArrayList<>(List.of(value)));
                } else {
                    held.get(at).add(value);
                }
            }
            return new Groups(answers, held, unread);
        }

        /** The values a share draws: so many from each group, the first value again and again
         *  where a value may repeat and that many different ones where it may not. */
        List<Place> drawn(int[] share, boolean distinct) {
            List<Place> out = new ArrayList<>();
            for (int g = 0; g < share.length; g++) {
                for (int n = 0; n < share[g]; n++) {
                    out.add(values.get(g).get(distinct ? n : 0));
                }
            }
            return out;
        }

        String unreadSaid() {
            return "an element a statement could not be read at was not chosen: " + unread;
        }
    }

    /**
     * Every way of sharing a size out among the groups that meets every count, in the order the
     * groups were found and with the first group's share largest first.
     */
    private static final class Sharing {

        private final Groups groups;
        private final List<Asked> asked;
        private final NumericSet size;
        private final boolean distinct;

        /** How many more sharings this may look at, over every size it is asked for. */
        private int left;

        /** Whether a sharing was in front of the walk when there was no room left for it. */
        private boolean stopped;

        /**
         * Sharings of the elements among {@code groups} that meet everything {@code asked}.
         *
         * @param most how many sharings this looks at, over every size it is asked for
         */
        Sharing(Groups groups, List<Asked> asked, NumericSet size, boolean distinct, int most) {
            this.groups = groups;
            this.asked = asked;
            this.size = size;
            this.distinct = distinct;
            this.left = most;
        }

        /**
         * Hands each sharing of {@code elements} that meets every count to {@code take}, in order,
         * until {@code take} answers that it has enough or the sharings this may look at are
         * spent.
         *
         * @return whether every sharing of that size was looked at
         */
        boolean each(int elements, Predicate<int[]> take) {
            if (size != null && !size.holds(Count.of(elements), Carrier.WHOLE)) {
                return true;
            }
            return share(new int[groups.answers().size()], 0, elements, take);
        }

        /** Whether a sharing was left unlooked at for the figure, which is what the walk was
         *  stopped by and not the sharings running out. */
        boolean spent() {
            return stopped;
        }

        private boolean share(int[] share, int g, int remaining, Predicate<int[]> take) {
            if (g == share.length) {
                if (remaining != 0) {
                    return true;
                }
                if (left == 0) {
                    stopped = true;
                    return false;
                }
                left--;
                return !meetsEveryCount(share) || take.test(share.clone());
            }
            int most = distinct ? Math.min(remaining, groups.values().get(g).size()) : remaining;
            for (int n = most; n >= 0; n--) {
                share[g] = n;
                if (!share(share, g + 1, remaining - n, take)) {
                    share[g] = 0;
                    return false;
                }
            }
            share[g] = 0;
            return true;
        }

        private boolean meetsEveryCount(int[] share) {
            for (int i = 0; i < asked.size(); i++) {
                int meeting = 0;
                for (int g = 0; g < share.length; g++) {
                    if (groups.answers().get(g)[i]) {
                        meeting += share[g];
                    }
                }
                if (!asked.get(i).asMany(meeting)) {
                    return false;
                }
            }
            return true;
        }
    }

    /**
     * Whether a container of {@code values}, read as a row's container is, has as many elements
     * meeting each statement as its count asks — every count the reading leaves it, where an
     * element could not be read.
     */
    private static boolean readsAsAsked(List<Asked> asked, TermPath container,
                                        Element element, Map<TermPath, ObservedValue> written,
                                        List<Place> values) {
        List<ObservedValue> observed = new ArrayList<>();
        for (Place each : values) {
            observed.add(element.carrier().valueOf(each));
        }
        AnElementRead whole = new AnElementRead(container, element.term().subjectPath(), written,
                observed);
        for (Asked each : asked) {
            if (!(each.over(container, values, whole) instanceof AStatementAtARow.Answer.Holds)) {
                return false;
            }
        }
        return true;
    }

    /** The container holding an element for each value, under the names both wear. */
    private static FixtureTemplate holdingThese(List<Place> values, Carrier carrier, TypeView view,
                                                TypeView ofTheElement,
                                                RuleReadingSource ruleSource) {
        List<FixtureTemplate> elements = new ArrayList<>();
        for (Place each : values) {
            FixtureTemplate one = WornNames.under(ofTheElement.wrappers(),
                    FixtureTemplate.on(carrier, each, ruleSource.symbols().scope()::reach),
                    ruleSource);
            if (one == null) {
                return null;
            }
            elements.add(one);
        }
        return WornNames.under(view.wrappers(), FixtureTemplate.collection(elements), ruleSource);
    }

    /**
     * A row holding nothing but a container of these elements and the numbers beside them, read
     * the way a row is.
     *
     * <p>Each element is a reading of its own ({@link #elements}), and the container is walked
     * through them. Anything else the statements ask for — a position this does not hold, the
     * elements of another container — could not be walked, which a statement reads as not being
     * able to tell and never as failing.
     */
    private record AnElementRead(TermPath container, TermPath element,
                                 Map<TermPath, ObservedValue> written,
                                 List<ObservedValue> held) implements BorderQuantity.Observation {

        /** Each element, read as this row with that element chosen. */
        List<BorderQuantity.Observation> elements() {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (ObservedValue each : held) {
                out.add(new AnElementRead(container, element, written, List.of(each)));
            }
            return out;
        }

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            if (path.equals(element)) {
                return held.size() == 1
                        ? WalkResult.reached(new ObservationAtPoint.Value(held.getFirst()))
                        : WalkResult.couldNotWalk();
            }
            ObservedValue value = written.get(path);
            return value == null ? WalkResult.couldNotWalk()
                    : WalkResult.reached(new ObservationAtPoint.Value(value));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            return path.equals(element) ? WalkResult.reached(held) : WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath of) {
            return of.equals(container) ? WalkResult.reached(elements())
                    : WalkResult.couldNotWalk();
        }
    }

    private static TermRealizations.Realization none(String why) {
        return new TermRealizations.Realization.None(
                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, why);
    }

    /** Elements of a kind nothing here chooses, which is the population and no proof. */
    private static TermRealizations.Realization notChosen(String why) {
        return new TermRealizations.Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)), why);
    }

    private CardinalityComposer() {}
}
