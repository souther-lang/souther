package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line whose values in a case are what the case's own statements on them keep
 * ({@link CasesOfALineAsked.KeptByItsStatements}) is asked of the sets of those statements, and
 * comes to what choosing every case comes to.
 *
 * <p>Put to a world written here: a row is a truth for each of a few places, the line's values run
 * from nought to nine and no row's truths narrow them, and a statement on the values holds them to
 * one end. A case is asked as {@code WaysToACase#crossing} asks one: no row where no row of the
 * world meets it, and otherwise whether what its statements leave runs on both sides of the line,
 * read as {@code Cutting#leftBy} reads them — through its parts and its alternatives. The set of
 * statements asked of the line is given the same reading, so what is held is the asking and not
 * the world.
 */
class ALineKeptByACasesOwnStatementsIsAskedOfTheirSetsTest {

    /** Where the line is drawn: a value is below it or at it and above. */
    private static final int LINE = 5;

    /** How many values the line's quantity runs over. */
    private static final int VALUES = 10;

    private static final List<String> KEEPING = List.of("k0", "k1", "k2");

    private static final List<String> OTHERS = List.of("o0", "o1", "o2");

    /** The end each statement on the line's values holds them to, where it holds: at or above
     *  this, or below its negation. */
    private static final Map<String, Integer> FROM = Map.of("k0", 3, "k1", 6, "k2", 8);

    private static Proposition.Truth truth(String at, boolean holds) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), holds);
    }

    /** A world: which assignments of the places are rows. */
    private record World(List<Map<String, Boolean>> rows) {

        boolean holds(Proposition stated, Map<String, Boolean> row) {
            return switch (stated) {
                case Proposition.Truth truth -> row.get(placeOf(truth)) == truth.holds();
                case Proposition.All all -> all.parts().stream().allMatch(part -> holds(part, row));
                case Proposition.Any any -> any.parts().stream().anyMatch(part -> holds(part, row));
                case Proposition.Always always -> always.holds();
                default -> throw new IllegalArgumentException("not of this world: " + stated);
            };
        }

        boolean someRow(Proposition stated) {
            return rows.stream().anyMatch(row -> holds(stated, row));
        }

        /** What {@code stated} keeps the line's values to, read as a line reads it: null where it
         *  says nothing of them. */
        static BitSet leftBy(Proposition stated) {
            return switch (stated) {
                case Proposition.Truth truth when KEEPING.contains(placeOf(truth)) -> {
                    BitSet out = new BitSet();
                    int from = FROM.get(placeOf(truth));
                    if (truth.holds()) {
                        out.set(from, VALUES);
                    } else {
                        out.set(0, from);
                    }
                    yield out;
                }
                case Proposition.All all -> {
                    BitSet out = null;
                    for (Proposition part : all.parts()) {
                        BitSet one = leftBy(part);
                        if (one != null) {
                            if (out == null) {
                                out = (BitSet) one.clone();
                            } else {
                                out.and(one);
                            }
                        }
                    }
                    yield out;
                }
                case Proposition.Any any -> {
                    BitSet out = new BitSet();
                    for (Proposition part : any.parts()) {
                        BitSet one = leftBy(part);
                        if (one == null) {
                            yield null;
                        }
                        out.or(one);
                    }
                    yield out;
                }
                default -> null;
            };
        }

        /** Whether values kept to {@code kept} run on both sides of the line. */
        static boolean bothSides(BitSet kept) {
            BitSet values = kept == null ? everyValue() : kept;
            return values.nextSetBit(0) >= 0 && values.nextSetBit(0) < LINE
                    && values.nextSetBit(LINE) >= 0;
        }

        CasesOfALineAsked.Crossing crossing(Proposition condition) {
            if (!someRow(condition)) {
                return CasesOfALineAsked.Crossing.NO_ROWS;
            }
            return bothSides(leftBy(condition)) ? CasesOfALineAsked.Crossing.MAY_CROSS
                    : CasesOfALineAsked.Crossing.CANNOT_CROSS;
        }

        CasesOfALineAsked.KeptByItsStatements kept() {
            return new CasesOfALineAsked.KeptByItsStatements() {

                @Override
                public CasesOfALineAsked.Keeping keeping(Proposition part) {
                    if (part instanceof Proposition.Truth truth
                            && KEEPING.contains(placeOf(truth))) {
                        return CasesOfALineAsked.Keeping.ITSELF;
                    }
                    return keepsInside(part) ? CasesOfALineAsked.Keeping.INSIDE
                            : CasesOfALineAsked.Keeping.NOTHING;
                }

                @Override
                public boolean divides(Proposition statements) {
                    return bothSides(leftBy(statements));
                }
            };
        }

        private static boolean keepsInside(Proposition stated) {
            return stated.partsHeld().stream().anyMatch(part -> (part instanceof Proposition.Truth
                    truth && KEEPING.contains(placeOf(truth))) || keepsInside(part));
        }
    }

    private static String placeOf(Proposition.Truth truth) {
        List<String> places = new ArrayList<>(KEEPING);
        places.addAll(OTHERS);
        return places.stream()
                .filter(at -> truth.of().equals(new DecisionSubject.AnInput(TermPath.of(at))))
                .findFirst().orElseThrow();
    }

    private static BitSet everyValue() {
        BitSet out = new BitSet();
        out.set(0, VALUES);
        return out;
    }

    /** A random world over every place: some of the assignments are rows. */
    private static World worldOf(Random random) {
        List<String> places = new ArrayList<>(KEEPING);
        places.addAll(OTHERS);
        List<Map<String, Boolean>> rows = new ArrayList<>();
        for (int assigned = 0; assigned < 1 << places.size(); assigned++) {
            if (random.nextInt(8) != 0) {
                continue;
            }
            Map<String, Boolean> row = new HashMap<>();
            for (int at = 0; at < places.size(); at++) {
                row.put(places.get(at), (assigned & 1 << at) != 0);
            }
            rows.add(row);
        }
        return new World(rows);
    }

    /** A random statement of one or two places, a choice among them where {@code withChoices}. */
    private static Proposition partOf(Random random, boolean withChoices) {
        List<String> places = new ArrayList<>(KEEPING);
        places.addAll(OTHERS);
        Proposition first = truth(places.get(random.nextInt(places.size())), random.nextBoolean());
        if (random.nextInt(3) != 0) {
            return first;
        }
        Proposition second = truth(places.get(random.nextInt(places.size())),
                random.nextBoolean());
        return withChoices && random.nextBoolean() ? Proposition.any(List.of(first, second))
                : Proposition.all(List.of(first, second));
    }

    /** Several choices taken together, each among two or three cases of a statement or two. */
    private static DecidingCase.Cases casesOf(Random random, boolean withChoices) {
        List<DecidingCase.Cases> choices = new ArrayList<>();
        int many = 2 + random.nextInt(3);
        for (int choice = 0; choice < many; choice++) {
            List<DecidingCase.Cases> alternatives = new ArrayList<>();
            int ways = 2 + random.nextInt(2);
            for (int way = 0; way < ways; way++) {
                alternatives.add(new DecidingCase.Cases.One(partOf(random, withChoices)));
            }
            choices.add(new DecidingCase.Cases.EachOf(alternatives));
        }
        return new DecidingCase.Cases.Together(choices);
    }

    /**
     * Asked of the sets of its statements, a line is said in the case as it was said only where
     * every case with a row in it, chosen to the end, divides; and where it is not, it comes to
     * what choosing comes to. Choosing stops at a part chosen so far whose rows are on one side,
     * though no case past it may hold a row: the sets ask the cases past it, so they say the case
     * as it was said there too, and wherever choosing does. In some of the worlds the sets settle
     * it with fewer questions than choosing.
     */
    @Test
    void theCaseAsItWasSaidIsWhatEveryCaseWithARowDividesIn() {
        Random random = new Random(2994);
        int settledBySets = 0;
        int finerThanChoosing = 0;
        for (int round = 0; round < 600; round++) {
            World world = worldOf(random);
            DecidingCase.Cases cases = casesOf(random, round % 3 == 0);
            DecidingCase said = new DecidingCase(cases.holdingInSome(1 << 20).orElseThrow(), cases);
            List<Proposition> askedChoosing = new ArrayList<>();
            List<Proposition> askedBySets = new ArrayList<>();

            CasesOfALineAsked.Found chosen = CasesOfALineAsked.casesOf(said,
                    recording(world, askedChoosing));
            CasesOfALineAsked.Found bySets = CasesOfALineAsked.casesOf(said,
                    recording(world, askedBySets), world.kept());

            boolean everyCaseWithARowDivides = CasesOfALineAsked.atomsOf(said, world::crossing)
                    .each().stream().allMatch(atom ->
                            atom.answer() != CasesOfALineAsked.Crossing.CANNOT_CROSS);
            if (bySets.decidesIn().equals(List.of(said))) {
                assertTrue(everyCaseWithARowDivides, () -> "in " + world + " of " + cases);
                if (!chosen.equals(bySets)) {
                    finerThanChoosing++;
                }
            } else {
                assertEquals(chosen, bySets, () -> "in " + world + " of " + cases);
            }
            if (askedBySets.size() < askedChoosing.size()) {
                settledBySets++;
            }
        }
        int settled = settledBySets;
        int finer = finerThanChoosing;
        assertTrue(settled > 30, () -> "the sets settled too few worlds: " + settled);
        assertTrue(finer > 0, "no world had a part chosen so far on one side with no row past it");
    }

    /**
     * A row where a statement keeping the values to one side holds is no row of a case holding
     * that statement: it may be a row of another case, which says nothing of them. So the cases
     * holding it are asked, and not the cases said with it beside them.
     */
    @Test
    void aRowMeetingAStatementInACaseThatDoesNotHoldItIsNoRowOfTheCasesHoldingIt() {
        // k1 holds the values at six and above. The one row holds k1 and o1, and not o0: it is a
        // row of the case o1, which holds no statement on the values, and of no case holding k1.
        Proposition k1AndO0 = Proposition.all(List.of(truth("k1", true), truth("o0", true)));
        Proposition o1 = truth("o1", true);
        DecidingCase.Cases cases = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(k1AndO0), new DecidingCase.Cases.One(o1)));
        World world = new World(List.of(
                Map.of("k0", false, "k1", true, "k2", false, "o0", false, "o1", true,
                        "o2", false)));
        DecidingCase said = new DecidingCase(cases.holdingInSome(1 << 20).orElseThrow(), cases);
        assertNotEquals(CasesOfALineAsked.Crossing.NO_ROWS,
                world.crossing(Proposition.all(List.of(said.condition(), truth("k1", true)))),
                "the cases said, with k1 beside them, hold the row");
        List<Proposition> asked = new ArrayList<>();

        CasesOfALineAsked.Found found = CasesOfALineAsked.casesOf(said,
                recording(world, asked), world.kept());

        assertEquals(List.of(said), found.decidesIn());
        assertEquals(List.of(said.condition(), k1AndO0), asked,
                "the cases holding, and the one case holding k1, which no row is in");
    }

    private static Function<Proposition, CasesOfALineAsked.Crossing> recording(
            World world, List<Proposition> asked) {
        return condition -> {
            asked.add(condition);
            return world.crossing(condition);
        };
    }

    /**
     * Where every case with a row divides, the sets are asked and no case is chosen: what is asked
     * is the cases holding, and each smallest set of statements that leaves the values one side.
     */
    @Test
    void whereEveryCaseWithARowDividesNoCaseIsChosen() {
        // k1 holds the values at six and above, on one side of the line, and no row holds it; k2
        // not holding keeps them below eight, on both sides.
        Proposition k1 = truth("k1", true);
        Proposition notK2 = truth("k2", false);
        Proposition o0 = truth("o0", true);
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(List.of(
                new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(k1),
                        new DecidingCase.Cases.One(o0))),
                new DecidingCase.Cases.EachOf(List.of(new DecidingCase.Cases.One(notK2),
                        new DecidingCase.Cases.One(truth("o1", true))))));
        World world = new World(List.of(
                Map.of("k0", false, "k1", false, "k2", false, "o0", true, "o1", true,
                        "o2", false)));
        DecidingCase said = new DecidingCase(cases.holdingInSome(1 << 20).orElseThrow(), cases);
        List<Proposition> asked = new ArrayList<>();

        CasesOfALineAsked.Found found = CasesOfALineAsked.casesOf(said, condition -> {
            asked.add(condition);
            return world.crossing(condition);
        }, world.kept());

        assertEquals(List.of(said), found.decidesIn());
        assertEquals(List.of(said.condition(), k1), asked, "the cases holding, and the cases"
                + " holding k1, which keeps the values above the line, asked once where they"
                + " begin alike and left there");
    }
}
