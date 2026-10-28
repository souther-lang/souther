package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
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

    private static Term<String> term(String place, ExactRatio weight) {
        NumericDomain.Bounds held = run(LEAST, GREATEST);
        return new Term<>(List.of(place), weight, held, held, null, true,
                Granularity.DISCRETE, held, place);
    }

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
            for (int constant = -3; constant <= 3; constant++) {
                for (Rel relation : RELATIONS) {
                    for (int at = 0; at < program.weights().size(); at++) {
                        check(program, program.sums(), constant, relation, at);
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
                    check(compared, adding, constant, relation, at);
                }
            }
        }
    }

    private static void check(Program program, List<IntSum> sums, int constant, Rel relation,
                              int at) {
        int size = program.weights().size();
        List<Term<String>> terms = new ArrayList<>();
        for (int i = 0; i < size; i++) {
            terms.add(term(NAMES.get(i), program.weightOf(i)));
        }
        Leaves said = WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(constant),
                relation, String::equals, (one, other) -> true, Granularity.DISCRETE,
                BigInteger.valueOf(GREATEST), List.of(), new Operations(sums, program.state()));
        String where = program.name() + ", constant " + constant + " " + relation + " 0, term "
                + at + ": " + said;
        int range = GREATEST - LEAST + 1;
        // A row is a row of the program where it gets past every operation the program works out,
        // told or not: the code was given those it was told of.
        List<IntSum> everyOperation = new ArrayList<>(sums);
        everyOperation.addAll(program.hidden());
        // For each run it says, whether some value of it has a row that gets past the operations:
        // a run no row stands in settles nothing and is settled for want of one.
        int runsSaid = said instanceof Leaves.Settled settled ? settled.runs().size() : 0;
        boolean[] aRowStandsIn = new boolean[runsSaid];
        for (int value = LEAST; value <= GREATEST; value++) {
            boolean sawTrue = false;
            boolean sawFalse = false;
            int others = (int) Math.pow(range, size - 1);
            for (int code = 0; code < others; code++) {
                int[] row = new int[size];
                int rest = code;
                for (int i = 0; i < size; i++) {
                    if (i == at) {
                        row[i] = value;
                    } else {
                        row[i] = LEAST + rest % range;
                        rest /= range;
                    }
                }
                if (!getsPast(everyOperation, row)) {
                    continue;
                }
                ExactRatio form = ExactRatio.of(constant);
                for (int i = 0; i < size; i++) {
                    form = form.plus(program.weightOf(i).times(ExactRatio.of(row[i])).orNull())
                            .orNull();
                }
                if (holds(relation, form.signum())) {
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

    /** Whether every operation holds at the row, worked out and held to the ends of the type. */
    private static boolean getsPast(List<IntSum> sums, int[] row) {
        Map<Object, ExactRatio> values = new LinkedHashMap<>();
        for (int i = 0; i < row.length; i++) {
            values.put(NAMES.get(i), ExactRatio.of(row[i]));
        }
        for (IntSum each : sums) {
            ExactRatio at = each.at(values);
            if (at == null || at.compareTo(ExactRatio.of(LEAST)) < 0
                    || at.compareTo(ExactRatio.of(GREATEST)) > 0) {
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
