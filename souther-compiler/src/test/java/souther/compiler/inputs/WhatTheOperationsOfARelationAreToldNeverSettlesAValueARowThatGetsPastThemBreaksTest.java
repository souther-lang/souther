package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Beside;
import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Over a type that holds {@code -5} to {@code 4}, a relation asked of the operations the program
 * works out: whatever {@link Leaves} says of a term is true of every row that gets past those
 * operations, found by working each of them out at every row and holding it to the ends.
 *
 * <p>The rows are counted here and not read off the sizes the relation is cut as, so that the
 * check and the code do not share the account of what a row that is computed is. A value is said
 * settled only where every such row at it comes out as the run says, and left either way only
 * where such rows come out both.
 *
 * <p>The programs differ in what they work out for a relation that is one form: a sum added from
 * the left, from the right, with the constant added to it or only compared with it, and with
 * signs. The least value of the type is among the values, and the type holds one more below
 * nought than above it.
 */
class WhatTheOperationsOfARelationAreToldNeverSettlesAValueARowThatGetsPastThemBreaksTest {

    private static final int LEAST = -5;
    private static final int GREATEST = 4;
    private static final List<String> NAMES = List.of("a", "b", "c");

    private static NumericDomain.Bounds run(int low, int high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of((long) low)),
                Endpoint.inclusive(Count.of((long) high)));
    }

    /** A term that may hold every value of the type and is shown to take those of
     *  {@code realizes}: the rows are the ones with it anywhere it may hold. */
    private static Term<String> term(String place, ExactRatio weight,
                                     NumericDomain.Bounds realizes) {
        NumericDomain.Bounds held = run(LEAST, GREATEST);
        return new Term<>(List.of(place), weight, held, realizes, null, true,
                Granularity.DISCRETE, held, place);
    }

    /** What the terms are shown to take: all of the type, then one value at either end, then a
     *  pair in the middle. The rows are those with a term anywhere it may hold, whichever of
     *  these is shown. */
    private static final List<NumericDomain.Bounds> TAKEN =
            List.of(run(LEAST, GREATEST), run(GREATEST, GREATEST), run(LEAST, LEAST), run(0, 1));

    /** An operation over the named terms, each weighed by the number after it, and a constant. */
    private static IntSum sum(int constant, Object... namesAndWeights) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < namesAndWeights.length; i += 2) {
            coefs.put(namesAndWeights[i], ExactRatio.of((Integer) namesAndWeights[i + 1]));
        }
        return new IntSum(coefs, ExactRatio.of(constant), BigInteger.valueOf(LEAST),
                BigInteger.valueOf(GREATEST));
    }

    /**
     * What the program works out, and the weights the relation is cut with: each of {@code weights}
     * times {@code scale}, which a quotient by a number makes of the sum it divides.
     *
     * @param sums   the operations the reading told of
     * @param hidden the operations the program works out and the reading did not tell of: a row
     *               gets past those as well, and the code is not given them
     * @param state  how much of what can stop a run the reading told
     */
    private record Program(String name, List<Integer> weights, ExactRatio scale,
                           List<IntSum> sums, List<IntSum> hidden, Told state) {

        Program(String name, List<Integer> weights, ExactRatio scale, List<IntSum> sums,
                boolean exact) {
            this(name, weights, scale, sums, List.of(), exact ? Told.EVERY : Told.SOME);
        }

        Program(String name, List<Integer> weights, List<IntSum> sums, boolean exact) {
            this(name, weights, ExactRatio.ONE, sums, exact);
        }

        ExactRatio weightOf(int term) {
            return ExactRatio.of(weights.get(term)).times(scale).orNull();
        }
    }

    private static final List<Program> PROGRAMS = List.of(
            new Program("a >= b, nothing worked out", List.of(1, -1), List.of(), true),
            new Program("a + b", List.of(1, 1), List.of(sum(0, "a", 1, "b", 1)), true),
            new Program("a - b", List.of(1, -1), List.of(sum(0, "a", 1, "b", -1)), true),
            new Program("2 * a, then 2 * a + b", List.of(2, 1),
                    List.of(sum(0, "a", 2), sum(0, "a", 2, "b", 1)), true),
            new Program("a + 3, then b less that", List.of(-1, 1),
                    List.of(sum(3, "a", 1), sum(0, "a", -1, "b", 1)), true),
            new Program("(a + b) + c", List.of(1, 1, 1),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)), true),
            new Program("a + (b + c)", List.of(1, 1, 1),
                    List.of(sum(0, "b", 1, "c", 1), sum(0, "a", 1, "b", 1, "c", 1)), true),
            new Program("(a - b) - c", List.of(1, -1, -1),
                    List.of(sum(0, "a", 1, "b", -1), sum(0, "a", 1, "b", -1, "c", -1)), true),
            new Program("a - (b + c)", List.of(1, -1, -1),
                    List.of(sum(0, "b", 1, "c", 1), sum(0, "a", 1, "b", -1, "c", -1)), true),
            new Program("(a + b + c) / 3", List.of(1, 1, 1),
                    ExactRatio.of(1).dividedBy(ExactRatio.of(3)).orNull(),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)), true),
            new Program("(a + b + c) / 2", List.of(1, 1, 1),
                    ExactRatio.of(1).dividedBy(ExactRatio.of(2)).orNull(),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)), true),
            new Program("(a - b - c) / 2", List.of(1, -1, -1),
                    ExactRatio.of(1).dividedBy(ExactRatio.of(2)).orNull(),
                    List.of(sum(0, "b", 1, "c", 1), sum(0, "a", 1, "b", -1, "c", -1)), true),
            new Program("2 * (a + b + c)", List.of(1, 1, 1), ExactRatio.of(2),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1),
                            sum(0, "a", 2, "b", 2, "c", 2)), true),
            new Program("a + 4 - 4 + b + c", List.of(1, 1, 1),
                    List.of(sum(4, "a", 1), sum(0, "a", 1), sum(0, "a", 1, "b", 1),
                            sum(0, "a", 1, "b", 1, "c", 1)), true),
            // The sum worked out past the greatest value on the way and back: a row stops where
            // a + b + 4 does, which the form does not show.
            new Program("((a + b) + 4) - 4", List.of(1, 1),
                    List.of(sum(0, "a", 1, "b", 1), sum(4, "a", 1, "b", 1)), true),
            // The constant added a piece at a time.
            new Program("(a + 1) + 1 against b", List.of(1, -1),
                    List.of(sum(1, "a", 1), sum(2, "a", 1)), true),
            new Program("(a - 1) - 1 against b", List.of(1, -1),
                    List.of(sum(-1, "a", 1), sum(-2, "a", 1)), true),
            new Program("(a - 1) + 3 against b", List.of(1, -1),
                    List.of(sum(-1, "a", 1), sum(2, "a", 1)), true),
            new Program("((a + b) + 1) + c", List.of(1, 1, 1),
                    List.of(sum(0, "a", 1, "b", 1), sum(1, "a", 1, "b", 1),
                            sum(1, "a", 1, "b", 1, "c", 1)), true),
            new Program("a - 4 + 4 + b + c", List.of(1, 1, 1),
                    List.of(sum(-4, "a", 1), sum(0, "a", 1), sum(0, "a", 1, "b", 1),
                            sum(0, "a", 1, "b", 1, "c", 1)), true),
            new Program("(a + b) + c, the others not told", List.of(1, 1, 1),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)), false),
            // No reading was made, and the program adds the form up: the sizes of the form say it.
            new Program("a + b + c, no reading", List.of(1, 1, 1), ExactRatio.ONE, List.of(),
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)),
                    Told.NOTHING_SAID),
            // The reading met something that can stop a run and told of nothing for it: what a
            // row has to get past is more than the form shows, and no row is shown computed.
            new Program("a >= b, an untold a + 1", List.of(1, -1), ExactRatio.ONE, List.of(),
                    List.of(sum(1, "a", 1)), Told.SOME),
            new Program("a >= b, an untold a + 4", List.of(1, -1), ExactRatio.ONE, List.of(),
                    List.of(sum(4, "a", 1)), Told.SOME),
            new Program("a + b, an untold a + 4", List.of(1, 1), ExactRatio.ONE, List.of(),
                    List.of(sum(4, "a", 1), sum(0, "a", 1, "b", 1)), Told.SOME),
            new Program("a + b, a + b told and an untold b + 4", List.of(1, 1), ExactRatio.ONE,
                    List.of(sum(0, "a", 1, "b", 1)), List.of(sum(4, "b", 1)), Told.SOME),
            new Program("(a + b) + c, an untold c + 1", List.of(1, 1, 1), ExactRatio.ONE,
                    List.of(sum(0, "a", 1, "b", 1), sum(0, "a", 1, "b", 1, "c", 1)),
                    List.of(sum(1, "c", 1)), Told.SOME),
            // Compared with each other and nothing added is a fact of the form, and not of the
            // program: this one stops at the greatest a.
            new Program("(a + 1) - 1 >= b", List.of(1, -1),
                    List.of(sum(1, "a", 1), sum(0, "a", 1)), true));

    /** Every relation, the equalities among them: two terms compared with each other and nothing
     *  added are asked of a witness only for those. */
    private static final List<Rel> RELATIONS =
            List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ, Rel.NE);

    private static boolean holds(Rel relation, int signOfTheForm) {
        return relation.holds(signOfTheForm);
    }

    @Test
    void whatIsSaidOfATermIsTrueOfEveryRowThatGetsPastTheOperations() {
        for (Program program : PROGRAMS) {
            for (NumericDomain.Bounds taken : TAKEN) {
                for (int constant = -3; constant <= 3; constant++) {
                    for (Rel relation : RELATIONS) {
                        for (int at = 0; at < program.weights().size(); at++) {
                            check(program, program.sums(), constant, relation, at, taken);
                        }
                    }
                }
            }
        }
    }

    /** The form {@code a + b + c + k} held against nought as a program that adds {@code k} to the
     *  sum as one more operation, and as one that compares the sum with {@code -k}: the same
     *  form, and not the same rows. */
    @Test
    void aConstantTheProgramAddsIsNotOneItOnlyComparesTheSumWith() {
        Program compared = PROGRAMS.get(5);
        for (int constant = -3; constant <= 3; constant++) {
            List<IntSum> adding = new ArrayList<>(compared.sums());
            adding.add(sum(constant, "a", 1, "b", 1, "c", 1));
            for (Rel relation : RELATIONS) {
                for (int at = 0; at < 3; at++) {
                    check(compared, adding, constant, relation, at, TAKEN.getFirst());
                }
            }
        }
    }

    /**
     * The two-term programs again, asked of what two terms stand apart by instead of each term
     * alone ({@code a + b >= 2} compares the sum with 2 and adds no 2): the answer is the same
     * claim about the rows, so the same count of them holds it to account.
     */
    @Test
    void whatIsSaidOfATermByTheirDifferenceIsTrueOfEveryRowThatGetsPastTheOperations() {
        for (Program program : PROGRAMS) {
            if (program.weights().size() != 2 || program.weightOf(0).abs().compareTo(
                    ExactRatio.ONE) != 0) {
                continue;
            }
            for (NumericDomain.Bounds taken : TAKEN) {
                for (int constant = -3; constant <= 3; constant++) {
                    for (Rel relation : RELATIONS) {
                        for (int at = 0; at < 2; at++) {
                            List<Term<String>> terms = termsOf(program, taken);
                            Operations operations =
                                    new Operations(program.sums(), program.state());
                            Leaves said = WhatARelationLeavesUndivided.leavesByTheirDifference(
                                    terms, at, Beside.just(ExactRatio.of(constant)), relation,
                                    List.of(), String::equals, BigInteger.valueOf(GREATEST),
                                    operations, Map.of(), operations.theSizesAreRowsComputed(
                                            terms, ExactRatio.of(constant)));
                            verify(program, program.sums(), constant, relation, at, said, -1, 0);
                        }
                    }
                }
            }
        }
    }

    /**
     * The three-term programs asked of two terms with the third held still at a value: what the
     * two are asked against is the constant and the third's weighed value, kept apart, since the
     * arithmetic adds them as two addends and a value that cancels the constant in the sum still
     * counts in the sizes. What is said is held to the rows with the third at that value. The
     * program {@code a + b + c > 4} with {@code c} held at 4 is asked as {@code a + b > 0}, and
     * {@code a = 0, b = 1} is no row of it: {@code 0 + 1 + 4} passes the type.
     *
     * <p>Not asked of a program no reading was made of: it is taken to add the form up with the
     * sizes symmetric about nought, which leave out the least value of the type, and what is
     * said of it is that approximation and not a claim about the rows.
     */
    @Test
    void whatIsSaidOfTwoTermsWithAThirdHeldStillIsTrueOfEveryRowWithTheThirdThere() {
        for (Program program : PROGRAMS) {
            if (program.weights().size() != 3 || program.weightOf(0).abs().compareTo(
                    ExactRatio.ONE) != 0 || program.weightOf(1).abs().compareTo(
                    ExactRatio.ONE) != 0 || program.state() == Told.NOTHING_SAID) {
                continue;
            }
            Operations operations = new Operations(program.sums(), program.state());
            // To the ends of the type: a constant the third's value cancels in the sum is as
            // large as the type is.
            for (NumericDomain.Bounds taken : TAKEN) {
                List<Term<String>> all = termsOf(program, taken);
                for (int constant = LEAST; constant <= GREATEST; constant++) {
                    boolean sizesAreRowsComputed =
                            operations.theSizesAreRowsComputed(all, ExactRatio.of(constant));
                    for (int held = LEAST; held <= GREATEST; held++) {
                        Beside beside = new Beside(List.of(ExactRatio.of(constant),
                                program.weightOf(2).times(ExactRatio.of(held)).orNull()));
                        for (Rel relation : RELATIONS) {
                            for (int at = 0; at < 2; at++) {
                                Leaves said =
                                        WhatARelationLeavesUndivided.leavesByTheirDifference(
                                                all.subList(0, 2), at, beside, relation,
                                                List.of(), String::equals,
                                                BigInteger.valueOf(GREATEST), operations,
                                                Map.of(NAMES.get(2), ExactRatio.of(held)),
                                                sizesAreRowsComputed);
                                verify(program, program.sums(), constant, relation, at, said, 2,
                                        held);
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * The check above holds for an answer of nothing, so it is held to say something too: a
     * program whose every operation is told, and that reads the two terms and the third held
     * still, settles a value by the rows of its operations, one program at a time. Held to the
     * rows by the checks above, a count of the answers is what a recovery is held to.
     */
    @Test
    void aProgramWhoseOperationsAreAllToldSettlesValuesByTheRowsTheyCompute() {
        Map<String, Integer> said = new LinkedHashMap<>();
        for (Program program : PROGRAMS) {
            if (program.state() != Told.EVERY || program.sums().isEmpty()
                    || program.weightOf(0).abs().compareTo(ExactRatio.ONE) != 0
                    || program.weightOf(1).abs().compareTo(ExactRatio.ONE) != 0
                    || program.weights().size() > 3) {
                continue;
            }
            Operations operations = new Operations(program.sums(), program.state());
            List<Term<String>> all = termsOf(program);
            int heldFrom = program.weights().size() == 3 ? LEAST : 0;
            int heldTo = program.weights().size() == 3 ? GREATEST : 0;
            for (int constant = -3; constant <= 3; constant++) {
                for (int held = heldFrom; held <= heldTo; held++) {
                    Beside beside = program.weights().size() == 3
                            ? new Beside(List.of(ExactRatio.of(constant),
                                    program.weightOf(2).times(ExactRatio.of(held)).orNull()))
                            : Beside.just(ExactRatio.of(constant));
                    Map<Object, ExactRatio> standing = program.weights().size() == 3
                            ? Map.of(NAMES.get(2), ExactRatio.of(held)) : Map.of();
                    for (Rel relation : RELATIONS) {
                        for (int at = 0; at < 2; at++) {
                            Leaves leaves = WhatARelationLeavesUndivided.leavesByTheirDifference(
                                    all.subList(0, 2), at, beside, relation, List.of(),
                                    String::equals, BigInteger.valueOf(GREATEST), operations,
                                    standing, false);
                            if (leaves instanceof Leaves.Settled) {
                                said.merge(program.name(), 1, Integer::sum);
                            }
                        }
                    }
                }
            }
        }
        assertTrue(said.getOrDefault("a + b", 0) > 0, "a + b settles no value: " + said);
        assertTrue(said.getOrDefault("(a + b) + c", 0) > 0,
                "(a + b) + c settles no value with c held still: " + said);
        assertTrue(said.getOrDefault("a + (b + c)", 0) > 0,
                "a + (b + c) settles no value with c held still: " + said);
    }

    /**
     * The same three-term programs asked which places the two are left undivided at, with the
     * third held still: a place said so is reached either way at the middle of the type, where
     * there is a row with the third there that gets past the operations and holds the relation,
     * and one that fails it.
     */
    @Test
    void aPlaceSaidUndividedByTheirDifferenceHasARowEachWayWithTheThirdHeldStill() {
        int said = 0;
        for (Program program : PROGRAMS) {
            if (program.weights().size() != 3 || program.weightOf(0).abs().compareTo(
                    ExactRatio.ONE) != 0 || program.weightOf(1).abs().compareTo(
                    ExactRatio.ONE) != 0 || program.state() == Told.NOTHING_SAID) {
                continue;
            }
            Operations operations = new Operations(program.sums(), program.state());
            List<Term<String>> all = termsOf(program);
            // The two reach the whole type and take the same values, as the analysis asks.
            List<Term<String>> pair = new ArrayList<>();
            for (int i = 0; i < 2; i++) {
                pair.add(new Term<>(List.of(NAMES.get(i)), program.weightOf(i),
                        run(LEAST, GREATEST), NumericDomain.Bounds.OPEN, "n", true,
                        Granularity.DISCRETE, run(LEAST, GREATEST), NAMES.get(i)));
            }
            for (int constant = LEAST; constant <= GREATEST; constant++) {
                boolean sizesAreRowsComputed =
                        operations.theSizesAreRowsComputed(all, ExactRatio.of(constant));
                for (int held = LEAST; held <= GREATEST; held++) {
                    Beside beside = new Beside(List.of(ExactRatio.of(constant),
                            program.weightOf(2).times(ExactRatio.of(held)).orNull()));
                    for (Rel relation : RELATIONS) {
                        Set<String> places = WhatARelationLeavesUndivided.ofTheirDifference(
                                pair, beside, relation, List.of(),
                                new WhatARelationLeavesUndivided.WhereTheRepresentationStops(
                                        run(LEAST, GREATEST)),
                                String::equals, BigInteger.valueOf(GREATEST), operations,
                                sizesAreRowsComputed);
                        for (int at = 0; at < 2; at++) {
                            if (places.contains(NAMES.get(at))) {
                                said++;
                                verifyARowEachWay(program, constant, relation, at, held);
                            }
                        }
                    }
                }
            }
        }
        // The control: the check is held to places that were said.
        assertTrue(said > 0, "no place was ever said undivided");
    }

    private static void verifyARowEachWay(Program program, int constant, Rel relation, int at,
                                          int held) {
        List<IntSum> operations = new ArrayList<>(program.sums());
        operations.addAll(program.hidden());
        int[][] everyOperation = compiled(operations);
        int free = 3 - at - 2;
        for (int value : new int[] {-1, 0}) {
            boolean sawTrue = false;
            boolean sawFalse = false;
            for (int other = LEAST; other <= GREATEST; other++) {
                int[] row = new int[3];
                row[at] = value;
                row[2] = held;
                row[free] = other;
                if (!getsPast(everyOperation, row)) {
                    continue;
                }
                if (holds(relation, formAt(program, constant, row).signum())) {
                    sawTrue = true;
                } else {
                    sawFalse = true;
                }
            }
            assertTrue(sawTrue && sawFalse, "said undivided at term " + at + ", yet at the middle "
                    + value + " a side has no row with term 2 held at " + held + ": "
                    + program.name()
                    + ", constant " + constant + " " + relation + " 0");
        }
    }

    private static List<Term<String>> termsOf(Program program) {
        return termsOf(program, TAKEN.getFirst());
    }

    private static List<Term<String>> termsOf(Program program, NumericDomain.Bounds taken) {
        List<Term<String>> terms = new ArrayList<>();
        for (int i = 0; i < program.weights().size(); i++) {
            terms.add(term(NAMES.get(i), program.weightOf(i), taken));
        }
        return terms;
    }

    private static void check(Program program, List<IntSum> sums, int constant, Rel relation,
                              int at, NumericDomain.Bounds taken) {
        Leaves said = WhatARelationLeavesUndivided.leavesOf(termsOf(program, taken), at,
                ExactRatio.of(constant), relation, String::equals, (one, other) -> true,
                Granularity.DISCRETE, BigInteger.valueOf(GREATEST), List.of(),
                new Operations(sums, program.state()));
        verify(program, sums, constant, relation, at, said, -1, 0);
    }

    /**
     * Holds {@code said} of the term {@code at} to the rows of the program, those with the term
     * at {@code held} standing at {@code heldValue} where it is not negative.
     */
    private static void verify(Program program, List<IntSum> sums, int constant, Rel relation,
                               int at, Leaves said, int held, int heldValue) {
        int size = program.weights().size();
        String where = program.name() + ", constant " + constant + " " + relation + " 0, term "
                + at + (held < 0 ? "" : ", term " + held + " held at " + heldValue) + ": " + said;
        int range = GREATEST - LEAST + 1;
        // A row is a row of the program where it gets past every operation the program works out,
        // told or not: the code was given those it was told of.
        List<IntSum> operations = new ArrayList<>(sums);
        operations.addAll(program.hidden());
        int[][] everyOperation = compiled(operations);
        // For each run it says, whether some value of it has a row that gets past the operations:
        // a run no row stands in settles nothing and is settled for want of one.
        int runsSaid = said instanceof Leaves.Settled settled ? settled.runs().size() : 0;
        boolean[] aRowStandsIn = new boolean[runsSaid];
        for (int value = LEAST; value <= GREATEST; value++) {
            boolean sawTrue = false;
            boolean sawFalse = false;
            int others = (int) Math.pow(range, size - (held < 0 ? 1 : 2));
            for (int code = 0; code < others; code++) {
                int[] row = new int[size];
                int rest = code;
                for (int i = 0; i < size; i++) {
                    if (i == at) {
                        row[i] = value;
                    } else if (i == held) {
                        row[i] = heldValue;
                    } else {
                        row[i] = LEAST + rest % range;
                        rest /= range;
                    }
                }
                if (!getsPast(everyOperation, row)) {
                    continue;
                }
                if (holds(relation, formAt(program, constant, row).signum())) {
                    sawTrue = true;
                } else {
                    sawFalse = true;
                }
            }
            if (said instanceof Leaves.Undivided) {
                assertTrue(!(sawTrue || sawFalse) || (sawTrue && sawFalse),
                        "undivided, yet only one side has a row at " + value + ": " + where);
            }
            if (said instanceof Leaves.Settled settled) {
                for (int i = 0; i < settled.runs().size(); i++) {
                    SettledRun each = settled.runs().get(i);
                    if (contains(each, value)) {
                        assertTrue(each.holds() ? !sawFalse : !sawTrue,
                                "settled " + each.holds() + " at " + value
                                        + ", yet a row that gets past the operations breaks it: "
                                        + where);
                        aRowStandsIn[i] |= sawTrue || sawFalse;
                    }
                }
            }
        }
        // The values past the rows that are computed are settled on purpose, as lines of the type
        // alone ({@code ofTheTypeAlone}); every other run has a row.
        boolean ofTheModel = said instanceof Leaves.Settled settled
                && settled.ofTheTypeAlone().isEmpty();
        for (int i = 0; i < runsSaid && ofTheModel; i++) {
            assertTrue(aRowStandsIn[i], "a run is settled that no row gets past the operations"
                    + " in: " + where);
        }
    }

    /**
     * The operations as whole numbers, once, for the many rows each is worked out at: the
     * constant, then the weight of each named term. The rows are counted without the code's own
     * arithmetic, and without allocating a ratio for each.
     */
    private static int[][] compiled(List<IntSum> sums) {
        int[][] out = new int[sums.size()][NAMES.size() + 1];
        for (int k = 0; k < sums.size(); k++) {
            out[k][0] = sums.get(k).constant().floor().orNull().intValueExact();
            for (int i = 0; i < NAMES.size(); i++) {
                ExactRatio weight = sums.get(k).coefs().get(NAMES.get(i));
                out[k][i + 1] = weight == null ? 0 : weight.floor().orNull().intValueExact();
            }
        }
        return out;
    }

    /** The form at the row: the constant, and the terms weighed, all the weights times
     *  {@code scale}. */
    private static ExactRatio formAt(Program program, int constant, int[] row) {
        int weighed = 0;
        for (int i = 0; i < row.length; i++) {
            weighed += program.weights().get(i) * row[i];
        }
        return ExactRatio.of(constant).plus(program.scale().times(ExactRatio.of(weighed)).orNull())
                .orNull();
    }

    /** Whether every operation holds at the row, worked out and held to the ends of the type. */
    private static boolean getsPast(int[][] sums, int[] row) {
        for (int[] each : sums) {
            int at = each[0];
            for (int i = 0; i < row.length; i++) {
                at += each[i + 1] * row[i];
            }
            if (at < LEAST || at > GREATEST) {
                return false;
            }
        }
        return true;
    }

    private static boolean contains(SettledRun each, int value) {
        ExactRatio v = ExactRatio.of(value);
        boolean fromOk = each.from() == null || each.from().at() == null
                || each.from().at().compareTo(v) <= 0;
        boolean toOk = each.to() == null || each.to().at() == null
                || v.compareTo(each.to().at()) <= 0;
        return fromOk && toOk;
    }
}
