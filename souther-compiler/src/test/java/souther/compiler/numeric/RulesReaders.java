package souther.compiler.numeric;

import souther.compiler.numeric.AffineReduction.Reduction;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.boxed;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.positionsOf;
import static souther.compiler.numeric.RulesAsWritten.twice;

/**
 * The readers of a set of rules that say what range each position is left in, and what is asked of
 * every one of them whatever it reads the rules for.
 *
 * <p>Three claims hold of a reader of rules, and a reader is held to each of them over the same
 * systems. What it says is the same whatever order the rules arrived in, and however often each was
 * said. And no point the rules admit is left outside what it says, which is checked against every
 * point of a bounded range and not sampled.
 *
 * <p>A claim is written once here and a reader is one entry of {@link #READERS}, so a reader added
 * is held to all three by being added, and a claim is changed in one place for every reader. What
 * only one reader answers for — that the difference bounds are tight, that a narrower box never
 * makes the reduction say less — stays with that reader.
 */
final class RulesReaders {

    static final int LOW = -4;
    static final int HIGH = 4;

    private RulesReaders() {
    }

    /**
     * What a reader said of some rules. {@code whole} is everything it said, which is what two
     * answers are equal by; {@code least} and {@code most} are the range it left a position in, the
     * part a point is asked against. A reader that found nothing left says {@link #NOTHING}.
     */
    record Said(Object whole, Function<String, ExactCut> least, Function<String, ExactCut> most) {

        static final Said NOTHING = new Said("nothing is left", null, null);

        boolean nothingLeft() {
            return least == null;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Said said && whole.equals(said.whole);
        }

        @Override
        public int hashCode() {
            return whole.hashCode();
        }

        @Override
        public String toString() {
            return whole.toString();
        }
    }

    interface Reader {
        String name();

        /** What this reader says of {@code rules}, said in the order given, over {@code positions}. */
        Said say(List<AffineConstraint<String>> rules, List<String> positions);
    }

    /** The orders to try the rules of a system in. */
    interface Orders {
        List<List<AffineConstraint<String>>> of(List<AffineConstraint<String>> stated);
    }

    /** How many of the answers narrowed a position and how many said nothing was left, so that a
     *  run that checked only one of the two can say so. */
    static final class Tally {
        int narrowed;
        int emptied;
        int systems;
    }

    static final List<Reader> READERS = List.of(
            reader("the closed state", RulesReaders::closedState),
            reader("the reduction", RulesReaders::reduction),
            reader("the difference bounds", RulesReaders::differenceBounds));

    private interface Saying {
        Said say(List<AffineConstraint<String>> rules, List<String> positions);
    }

    private static Reader reader(String name, Saying how) {
        return new Reader() {
            @Override
            public String name() {
                return name;
            }

            @Override
            public Said say(List<AffineConstraint<String>> rules, List<String> positions) {
                return how.say(rules, positions);
            }

            @Override
            public String toString() {
                return name;
            }
        };
    }

    private static Said closedState(List<AffineConstraint<String>> rules, List<String> positions) {
        ClosedState<String> closed = ClosedState.of(rules, atom -> Granularity.DISCRETE,
                CanonicalOrder.asTheyAreSpelled());
        if (closed.holdsNothing()) {
            return Said.NOTHING;
        }
        Box<String> box = closed.box();
        return new Said(box, box::leastOf, box::mostOf);
    }

    /** The reduction reads the rules against the range every position is held to, which is what a
     *  round of the closure hands it. Where the difference bounds alone hold nothing no round is
     *  reached, and that is nothing left too. */
    private static Said reduction(List<AffineConstraint<String>> rules, List<String> positions) {
        Box<String> from = between(positions);
        DifferenceBounds<String> differences =
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled());
        if (differences.holdsNothing()) {
            return Said.NOTHING;
        }
        Reduction<String> found = AffineReduction.over(
                FormReach.over(rules, from, differences, CanonicalOrder.asTheyAreSpelled()),
                atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled());
        if (!(found instanceof Reduction.Tightened<String> tightened)) {
            return Said.NOTHING;
        }
        Box<String> after = from.meeting(tightened.atLeast(), tightened.atMost());
        return new Said(tightened, after::leastOf, after::mostOf);
    }

    private static Said differenceBounds(List<AffineConstraint<String>> rules,
                                         List<String> positions) {
        DifferenceBounds<String> closed =
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled());
        if (closed.holdsNothing()) {
            return Said.NOTHING;
        }
        List<Object> told = new ArrayList<>();
        for (String position : positions) {
            told.add(closed.upperBoundOf(position));
            told.add(closed.lowerBoundOf(position));
            for (String apart : positions) {
                told.add(closed.differenceBound(position, apart));
            }
        }
        return new Said(told, closed::lowerBoundOf, closed::upperBoundOf);
    }

    /** The box holding every one of {@code positions} to {@link #LOW} to {@link #HIGH}. */
    static Box<String> between(List<String> positions) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : positions) {
            least.put(position, ExactCut.inclusive(ExactRatio.of(LOW)));
            most.put(position, ExactCut.inclusive(ExactRatio.of(HIGH)));
        }
        return new Box<>(least, most);
    }

    static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, atom -> Granularity.DISCRETE);
    }

    private static List<AffineConstraint<String>> followedBy(List<AffineConstraint<String>> first,
                                                              List<AffineConstraint<String>> then) {
        List<AffineConstraint<String>> out = new ArrayList<>(first);
        out.addAll(then);
        return out;
    }

    /**
     * What {@code reader} says of {@code system} is the same in every order of its rules the orders
     * name — bare, and with the range each position is held to said before them and after them. The
     * range holds a position each and nothing between two, so where it stands against the rules is
     * the one thing about its order a reader could answer differently for.
     */
    static void theOrderTheRulesArrivedInIsNotPartOfTheAnswer(Reader reader, List<Written> system,
                                                              Orders orders) {
        List<String> positions = List.copyOf(positionsOf(system));
        List<AffineConstraint<String>> stated = read(system);
        List<AffineConstraint<String>> range = read(boxed(List.of(), positions, LOW, HIGH));
        Said asWritten = reader.say(stated, positions);
        Said rangedAsWritten = reader.say(followedBy(range, stated), positions);
        for (List<AffineConstraint<String>> order : orders.of(stated)) {
            assertEquals(asWritten, reader.say(order, positions),
                    () -> reader + " moved when the rules were reordered: " + order);
            assertEquals(rangedAsWritten, reader.say(followedBy(range, order), positions),
                    () -> reader + " moved when the rules were reordered after the range: " + order);
            assertEquals(rangedAsWritten, reader.say(followedBy(order, range), positions),
                    () -> reader + " moved when the rules were reordered before the range: " + order);
        }
    }

    /** Saying a rule twice says what saying it once says. */
    static void sayingARuleTwiceSaysWhatSayingItOnceSays(Reader reader, List<Written> system) {
        List<String> positions = List.copyOf(positionsOf(system));
        List<AffineConstraint<String>> stated = read(system);
        assertEquals(reader.say(stated, positions), reader.say(twice(stated), positions),
                () -> reader + " said more of " + stated + " said twice");
    }

    /**
     * No point the rules admit is left outside what {@code reader} says of them. The direction
     * asserted is the only one that matters: a bound too tight refuses a row a model admits, and a
     * bound too loose merely says less than it could. Every position is held to the range, so the
     * points enumerated are all the points there are.
     *
     * <p>That nothing is left is proven one way only, so a reader saying it where the points hold
     * something is wrong and one saying it where they hold nothing is not asked anything more.
     */
    static void noPointTheRulesAdmitIsRefused(Reader reader, List<Written> system, Tally tally) {
        List<String> positions = List.copyOf(positionsOf(system));
        List<Written> written = boxed(system, positions, LOW, HIGH);
        List<Map<String, Integer>> admitted = pointsSatisfying(written, positions, LOW, HIGH);
        Said said = reader.say(read(written), positions);
        tally.systems++;
        if (said.nothingLeft()) {
            tally.emptied++;
            assertTrue(admitted.isEmpty(),
                    () -> reader + " said nothing is left, but " + written + " admits " + admitted);
            return;
        }
        boolean narrowed = false;
        for (String position : positions) {
            ExactCut least = said.least().apply(position);
            ExactCut most = said.most().apply(position);
            // Reductive: nothing came back wider than the range it was held to.
            assertEquals(least, ExactCut.tighterLower(ExactCut.inclusive(ExactRatio.of(LOW)), least));
            assertEquals(most, ExactCut.tighterUpper(ExactCut.inclusive(ExactRatio.of(HIGH)), most));
            narrowed |= !ExactCut.inclusive(ExactRatio.of(LOW)).equals(least)
                    || !ExactCut.inclusive(ExactRatio.of(HIGH)).equals(most);
            if (admitted.isEmpty()) {
                continue;
            }
            // A range holds every admitted point exactly when, at each position, it holds the least
            // and the greatest value an admitted point has there.
            int lowest = admitted.stream().mapToInt(point -> point.get(position)).min().orElseThrow();
            int highest = admitted.stream().mapToInt(point -> point.get(position)).max().orElseThrow();
            for (int value : new int[] {lowest, highest}) {
                assertTrue(admits(least, ExactRatio.of(value), false)
                                && admits(most, ExactRatio.of(value), true),
                        () -> reader + " refused a point the rules admit: " + position + " = " + value
                                + " under " + written + " left " + position + " in [" + least + ", "
                                + most + "]");
            }
        }
        if (narrowed) {
            tally.narrowed++;
        }
    }

    /** What a run that drew or chose its systems checked, said where it checked too little. */
    static void assertBothWaysWereChecked(Reader reader, Tally tally, int atLeastNarrowed) {
        assertTrue(tally.narrowed > atLeastNarrowed && tally.emptied > 0,
                () -> reader + " narrowed " + tally.narrowed + " and found " + tally.emptied
                        + " empty of " + tally.systems + ", so one of the two was checked too little");
    }
}
