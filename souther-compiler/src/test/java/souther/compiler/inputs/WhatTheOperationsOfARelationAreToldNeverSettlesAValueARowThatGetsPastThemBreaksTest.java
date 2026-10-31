package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Beside;
import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.OnTheDifference;
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
import java.util.function.Supplier;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    /**
     * What one term may hold, and what it is shown to take. What is true of the term is some set
     * of values between the two, and an answer has to be right for every such set: a value is
     * settled only if every row with the term anywhere it may hold comes out one way, and a
     * value is left either way, or has a row in its class, only if rows with the term at the
     * values it is shown to take do.
     *
     * @param low       the least value it may hold
     * @param high      the greatest
     * @param shownLow  the least value it is shown to take
     * @param shownHigh the greatest
     */
    private record Shape(int low, int high, int shownLow, int shownHigh) {

        NumericDomain.Bounds holds() {
            return run(low, high);
        }

        NumericDomain.Bounds realizes() {
            return run(shownLow, shownHigh);
        }

        boolean shows(int value) {
            return shownLow <= value && value <= shownHigh;
        }
    }

    private static final Shape FULL = new Shape(LEAST, GREATEST, LEAST, GREATEST);

    /** Anywhere in the type, and one value at the end shown to be taken. */
    private static final Shape SHOWN_ONE = new Shape(LEAST, GREATEST, GREATEST, GREATEST);

    /** One value at the end, which is all it may hold. */
    private static final Shape ONLY_THE_END = new Shape(GREATEST, GREATEST, GREATEST, GREATEST);

    /** Two values in the middle, both shown. */
    private static final Shape THE_MIDDLE = new Shape(0, 1, 0, 1);

    /** Two values in the middle, one of them shown. */
    private static final Shape THE_MIDDLE_SHOWN_ONE = new Shape(0, 1, 1, 1);

    /**
     * Every shape a term may have but the full one: what it may hold, and what it is shown to take
     * of that, are two ranges, and these differ in each — held anywhere and shown at an end, held
     * at the end alone, held in the middle and shown in all of it or in part.
     */
    private static final List<Shape> NARROWER =
            List.of(SHOWN_ONE, ONLY_THE_END, THE_MIDDLE, THE_MIDDLE_SHOWN_ONE);

    /**
     * The shapes of the two terms asked of: both the same, and each narrower with the other full.
     * A row has the other anywhere it may hold, so a value is settled or left either way by the
     * rows there, whichever of the two terms is the narrow one.
     */
    private static final List<List<Shape>> PAIRS = pairs();

    private static List<List<Shape>> pairs() {
        List<List<Shape>> out = new ArrayList<>();
        out.add(List.of(FULL, FULL));
        for (Shape each : NARROWER) {
            out.add(List.of(each, each));
            out.add(List.of(FULL, each));
            out.add(List.of(each, FULL));
        }
        return out;
    }

    /**
     * What a way states of the two terms asked of, each about how far apart they are: nothing,
     * their difference at nought or more, and at most two below. A row is one where each holds.
     */
    private static final List<List<OnTheDifference>> STATEMENTS = List.of(List.of(),
            List.of(new OnTheDifference(ExactRatio.ONE, ExactRatio.ZERO, Rel.GE)),
            List.of(new OnTheDifference(ExactRatio.ONE, ExactRatio.of(2), Rel.LE)));

    private static Term<String> term(String place, ExactRatio weight, Shape shape) {
        NumericDomain.Bounds order = run(LEAST, GREATEST);
        return new Term<>(List.of(place), weight, shape.holds(), shape.realizes(), null, true,
                Granularity.DISCRETE, order, place);
    }

    /** What the terms are shown to take, each full in what it may hold: all of the type, then
     *  one value at either end, then a pair in the middle. */
    private static final List<Shape> TAKEN =
            List.of(FULL, SHOWN_ONE, new Shape(LEAST, GREATEST, LEAST, LEAST),
                    new Shape(LEAST, GREATEST, 0, 1));

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

    /** The constants a relation is asked against. */
    private static final List<Integer> CONSTANTS_ASKED = List.of(-3, -2, -1, 0, 1, 2, 3);

    /**
     * The values a constant and a third term held still are asked at: every value of the type. A
     * sum of them with a term is held to the ends of the type, and the term it stops at moves with
     * each of them, so none stands for another.
     */
    private static final List<Integer> VALUES_ASKED =
            IntStream.rangeClosed(LEAST, GREATEST).boxed().toList();

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
            Map<Integer, RowsAt> rows = new LinkedHashMap<>();
            for (Shape taken : TAKEN) {
                for (int constant : CONSTANTS_ASKED) {
                    for (Rel relation : RELATIONS) {
                        for (int at = 0; at < program.weights().size(); at++) {
                            check(program, program.sums(), constant, relation, at, taken,
                                    rows.computeIfAbsent(at,
                                            each -> rowsOfATerm(program, program.sums(), each)));
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
            Map<Integer, RowsAt> rows = new LinkedHashMap<>();
            for (Rel relation : RELATIONS) {
                for (int at = 0; at < 3; at++) {
                    check(compared, adding, constant, relation, at, TAKEN.getFirst(),
                            rows.computeIfAbsent(at,
                                    each -> rowsOfATerm(compared, adding, each)));
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
            for (List<Shape> shapes : PAIRS) {
                for (List<OnTheDifference> statements : STATEMENTS) {
                    Map<Integer, RowsAt> rows = new LinkedHashMap<>();
                    for (int constant : CONSTANTS_ASKED) {
                        for (Rel relation : RELATIONS) {
                            for (int at = 0; at < 2; at++) {
                                List<Term<String>> terms = termsOf(program, shapes);
                                Operations operations =
                                        new Operations(program.sums(), program.state());
                                Leaves said =
                                        WhatARelationLeavesUndivided.leavesByTheirDifference(
                                                terms, at, Beside.just(ExactRatio.of(constant)),
                                                relation, statements, String::equals,
                                                BigInteger.valueOf(GREATEST), operations,
                                                Map.of(), operations.theSizesAreRowsComputed(
                                                        terms, ExactRatio.of(constant)));
                                verify(program, constant, relation, at, said, -1, 0, shapes,
                                        rows.computeIfAbsent(at, each -> rowsAt(program,
                                                program.sums(), each, -1, 0, shapes, statements)));
                            }
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
     *
     * <p>Asked at the values where the type's ends and nought decide it, and of the shapes that
     * tell which of the two terms is the narrow one.
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
            for (List<Shape> shapes : PAIRS) {
                List<Term<String>> all = termsOf(program, shapesOf(program, shapes));
                Map<Asked, RowsAt> rows = new LinkedHashMap<>();
                for (int constant : VALUES_ASKED) {
                    boolean sizesAreRowsComputed =
                            operations.theSizesAreRowsComputed(all, ExactRatio.of(constant));
                    for (int held : VALUES_ASKED) {
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
                                // The rows depend on where the third is held and which term is
                                // asked of, and not on the constant or the relation.
                                verify(program, constant, relation, at, said, 2, held,
                                        shapesOf(program, shapes),
                                        rows.computeIfAbsent(new Asked(at, held),
                                                each -> rowsAt(program, program.sums(), each.at(),
                                                        2, each.held(), shapesOf(program, shapes),
                                                        List.of())));
                            }
                        }
                    }
                }
            }
        }
    }

    /** Which term is asked of, and the value the third is held at. */
    private record Asked(int at, int held) {}

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
     * {@code ((a + b) + 4) - 4 >= 3} with {@code b} able to hold only the greatest value: the
     * sum {@code a + b + 4} stops every {@code a} from {@code -3}, so the rows are those of
     * {@code a} at {@code -5} and {@code -4}, and both fail. Those are the class of the model; the
     * values above them have no row, and are said as the type's alone, and no line the model
     * draws is put between a value with a row and one without.
     */
    @Test
    void aClassIsClaimedOnlyWhereARowWithTheOtherWhereItMayHoldIsComputed() {
        Program program = PROGRAMS.stream()
                .filter(each -> each.name().equals("((a + b) + 4) - 4")).findFirst().orElseThrow();
        List<Shape> shapes = List.of(FULL, ONLY_THE_END);
        List<Term<String>> terms = termsOf(program, shapes);
        Operations operations = new Operations(program.sums(), program.state());
        Leaves said = WhatARelationLeavesUndivided.leavesByTheirDifference(terms, 0,
                Beside.just(ExactRatio.of(-3)), Rel.GE, List.of(), String::equals,
                BigInteger.valueOf(GREATEST), operations, Map.of(), false);
        Leaves.Settled settled = (Leaves.Settled) said;
        assertEquals(List.of(), settled.linesOfTheModel());
        assertTrue(settled.runs().stream().anyMatch(each -> contains(each, -5)
                && contains(each, -4) && !each.holds()), settled.toString());
        assertTrue(!settled.ofTheTypeAlone().isEmpty(), settled.toString());
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

    /** Terms that are each of the shape {@code both}. */
    private static List<Term<String>> termsOf(Program program, Shape both) {
        return termsOf(program, both, both);
    }

    /** The terms of the program, the first two shaped as given and the rest full. */
    private static List<Term<String>> termsOf(Program program, Shape first, Shape second) {
        return termsOf(program, shapesOf(program, List.of(first, second)));
    }

    private static List<Term<String>> termsOf(Program program, List<Shape> shapes) {
        List<Term<String>> terms = new ArrayList<>();
        for (int i = 0; i < program.weights().size(); i++) {
            terms.add(term(NAMES.get(i), program.weightOf(i), shapes.get(i)));
        }
        return terms;
    }

    /** {@code firstTwo}, then a full shape for each term of the program beyond them. */
    private static List<Shape> shapesOf(Program program, List<Shape> firstTwo) {
        List<Shape> out = new ArrayList<>(firstTwo);
        while (out.size() < program.weights().size()) {
            out.add(FULL);
        }
        return out;
    }

    /** The rows a term asked of alone is held to: every term anywhere in the type. */
    private static RowsAt rowsOfATerm(Program program, List<IntSum> sums, int at) {
        return rowsAt(program, sums, at, -1, 0, shapesOf(program, List.of(FULL, FULL)),
                List.of());
    }

    private static void check(Program program, List<IntSum> sums, int constant, Rel relation,
                              int at, Shape taken, RowsAt rows) {
        Leaves said = WhatARelationLeavesUndivided.leavesOf(termsOf(program, taken), at,
                ExactRatio.of(constant), relation, String::equals, (one, other) -> true,
                Granularity.DISCRETE, BigInteger.valueOf(GREATEST), List.of(),
                new Operations(sums, program.state()));
        verify(program, constant, relation, at, said, -1, 0,
                shapesOf(program, List.of(FULL, FULL)), rows);
    }

    /** Whether each of {@code statements} holds at the row, about the sum of the first two terms
     *  where the program weighs them alike and their difference where not. */
    private static boolean statementsHold(Program program, List<OnTheDifference> statements,
                                          int[] row) {
        for (OnTheDifference each : statements) {
            int combined = program.weights().get(0).equals(program.weights().get(1))
                    ? row[0] + row[1] : row[0] - row[1];
            ExactRatio at = each.weight().times(ExactRatio.of(combined))
                    .flatMap(each.constant()::plus).orNull();
            if (!each.relation().holds(at.signum())) {
                return false;
            }
        }
        return true;
    }

    /**
     * What a row that gets past the operations weighs, scaled as the form is, and whether every
     * term of it but the one asked of is at a value it is shown to take. Rows alike in both say
     * the same of every constant and every relation, so one stands for them.
     */
    private record Weighed(ExactRatio scaled, boolean shown) {}

    /**
     * The rows of a program that get past its operations, by the value of the term asked of.
     * Which rows those are does not turn on the constant or the relation held to them, so they
     * are worked out once for the many of each that are asked.
     *
     * @param low     the least value of the term asked of
     * @param byValue for each value from {@code low} on, what its rows weigh
     */
    private record RowsAt(int low, List<List<Weighed>> byValue) {}

    /**
     * The rows of the program with the term {@code at} at each value it may hold, every other term
     * anywhere it may hold, and the term {@code held} at {@code heldValue} where it is not
     * negative, that get past the operations and the {@code statements}.
     */
    private static RowsAt rowsAt(Program program, List<IntSum> sums, int at, int held,
                                 int heldValue, List<Shape> shapes,
                                 List<OnTheDifference> statements) {
        int size = program.weights().size();
        // A row is a row of the program where it gets past every operation the program works out,
        // told or not: the code was given those it was told of.
        List<IntSum> operations = new ArrayList<>(sums);
        operations.addAll(program.hidden());
        int[][] everyOperation = compiled(operations);
        int others = 1;
        for (int i = 0; i < size; i++) {
            others *= i == at || i == held ? 1 : shapes.get(i).high() - shapes.get(i).low() + 1;
        }
        List<List<Weighed>> byValue = new ArrayList<>();
        // The values the term may hold are the ones asked of, and a row has each other term at
        // any value it may hold.
        for (int value = shapes.get(at).low(); value <= shapes.get(at).high(); value++) {
            Map<Integer, Weighed> distinct = new LinkedHashMap<>();
            for (int code = 0; code < others; code++) {
                int[] row = new int[size];
                boolean shown = true;
                int rest = code;
                for (int i = 0; i < size; i++) {
                    if (i == at) {
                        row[i] = value;
                    } else if (i == held) {
                        row[i] = heldValue;
                    } else {
                        int range = shapes.get(i).high() - shapes.get(i).low() + 1;
                        row[i] = shapes.get(i).low() + rest % range;
                        shown &= shapes.get(i).shows(row[i]);
                        rest /= range;
                    }
                }
                if (!getsPast(everyOperation, row) || !statementsHold(program, statements, row)) {
                    continue;
                }
                int weighed = weighedAt(program, row);
                boolean allShown = shown;
                distinct.computeIfAbsent(weighed * 2 + (allShown ? 1 : 0), each -> new Weighed(
                        program.scale().times(ExactRatio.of(weighed)).orNull(), allShown));
            }
            byValue.add(List.copyOf(distinct.values()));
        }
        return new RowsAt(shapes.get(at).low(), List.copyOf(byValue));
    }

    /**
     * Holds {@code said} of the term {@code at} to the rows of the program, those with the term
     * at {@code held} standing at {@code heldValue} where it is not negative.
     */
    private static void verify(Program program, int constant, Rel relation, int at, Leaves said,
                               int held, int heldValue, List<Shape> shapes, RowsAt rows) {
        // Said only of a case that fails, which is none of the many that hold.
        Supplier<String> where = () -> program.name() + ", constant " + constant + " " + relation
                + " 0, term " + at + (held < 0 ? "" : ", term " + held + " held at " + heldValue)
                + ", shapes " + shapes + ": " + said;
        // For each run it says, whether some value of it has a row that gets past the operations:
        // a run no row stands in settles nothing and is settled for want of one.
        int runsSaid = said instanceof Leaves.Settled settled ? settled.runs().size() : 0;
        boolean[] aRowStandsIn = new boolean[runsSaid];
        for (int value = rows.low(); value < rows.low() + rows.byValue().size(); value++) {
            // The rows with each other term anywhere it may hold, and among them the ones with
            // each at a value it is shown to take.
            boolean sawTrue = false;
            boolean sawFalse = false;
            boolean shownTrue = false;
            boolean shownFalse = false;
            for (Weighed row : rows.byValue().get(value - rows.low())) {
                ExactRatio form = ExactRatio.of(constant).plus(row.scaled()).orNull();
                if (holds(relation, form.signum())) {
                    sawTrue = true;
                    shownTrue |= row.shown();
                } else {
                    sawFalse = true;
                    shownFalse |= row.shown();
                }
            }
            // Left either way is shown by rows of values taken, wherever there is a row at all.
            if (said instanceof Leaves.Undivided) {
                int at0 = value;
                boolean one = sawTrue || sawFalse;
                boolean both = shownTrue && shownFalse;
                assertTrue(!one || both, () -> "undivided, yet only one side has a row shown at "
                        + at0 + ": " + where.get());
            }
            if (said instanceof Leaves.Settled settled) {
                for (int i = 0; i < settled.runs().size(); i++) {
                    SettledRun each = settled.runs().get(i);
                    if (contains(each, value)) {
                        int at0 = value;
                        boolean sawTheOtherWay = each.holds() ? sawFalse : sawTrue;
                        assertTrue(!sawTheOtherWay, () -> "settled " + each.holds() + " at " + at0
                                + ", yet a row that gets past the operations breaks it: "
                                + where.get());
                        aRowStandsIn[i] |= shownTrue || shownFalse;
                    }
                }
            }
        }
        // The values past the rows that are computed are settled on purpose, as lines of the type
        // alone ({@code ofTheTypeAlone}); every other run has a row.
        boolean ofTheModel = said instanceof Leaves.Settled settled
                && settled.ofTheTypeAlone().isEmpty();
        for (int i = 0; i < runsSaid && ofTheModel; i++) {
            assertTrue(aRowStandsIn[i], () -> "a run is settled that no row gets past the"
                    + " operations in: " + where.get());
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

    /** The terms of the row weighed, before the form's scale. */
    private static int weighedAt(Program program, int[] row) {
        int weighed = 0;
        for (int i = 0; i < row.length; i++) {
            weighed += program.weights().get(i) * row[i];
        }
        return weighed;
    }

    /** The form at the row: the constant, and the terms weighed, all the weights times
     *  {@code scale}. */
    private static ExactRatio formAt(Program program, int constant, int[] row) {
        return ExactRatio.of(constant)
                .plus(program.scale().times(ExactRatio.of(weighedAt(program, row))).orNull())
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
