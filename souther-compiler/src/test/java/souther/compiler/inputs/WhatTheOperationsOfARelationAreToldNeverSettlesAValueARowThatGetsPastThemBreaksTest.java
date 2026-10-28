package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.WhatARelationLeavesUndivided.IntSum;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Leaves;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.SettledRun;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
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
 */
class WhatTheOperationsOfARelationAreToldNeverSettlesAValueARowThatGetsPastThemBreaksTest {

    private static final int LEAST = -5;
    private static final int GREATEST = 4;

    private static NumericDomain.Bounds run(int low, int high) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of((long) low)),
                Endpoint.inclusive(Count.of((long) high)));
    }

    private static Term<String> term(String place, int weight) {
        NumericDomain.Bounds held = run(LEAST, GREATEST);
        return new Term<>(List.of(place), ExactRatio.of(weight), held, held, null, true,
                Granularity.DISCRETE, held, place);
    }

    private static IntSum sum(int constant, Object... namesAndWeights) {
        Map<Object, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < namesAndWeights.length; i += 2) {
            coefs.put(namesAndWeights[i], ExactRatio.of((Integer) namesAndWeights[i + 1]));
        }
        return new IntSum(coefs, ExactRatio.of(constant), BigInteger.valueOf(LEAST),
                BigInteger.valueOf(GREATEST));
    }

    /** What the program works out for a relation of two terms, and the weights it is cut with. */
    private record Program(String name, int first, int second, List<IntSum> sums, boolean exact) { }

    private static final List<Program> PROGRAMS = List.of(
            new Program("a >= b, nothing worked out", 1, -1, List.of(), true),
            new Program("a + b", 1, 1, List.of(sum(0, "a", 1, "b", 1)), true),
            new Program("a - b", 1, -1, List.of(sum(0, "a", 1, "b", -1)), true),
            new Program("2 * a, then a - b with b doubled", 2, -1,
                    List.of(sum(0, "a", 2), sum(0, "a", 2, "b", -1)), true),
            new Program("2 * a + b", 2, 1,
                    List.of(sum(0, "a", 2), sum(0, "a", 2, "b", 1)), true),
            new Program("a + 3, then b - that", -1, 1,
                    List.of(sum(3, "a", 1), sum(0, "a", -1, "b", 1)), true),
            new Program("a + b, others not told", 1, 1, List.of(sum(0, "a", 1, "b", 1)), false));

    private static boolean holds(Rel relation, int form) {
        return relation.holds(Integer.signum(form));
    }

    @Test
    void whatIsSaidOfATermIsTrueOfEveryRowThatGetsPastTheOperations() {
        for (Program program : PROGRAMS) {
            for (int constant = -3; constant <= 3; constant++) {
                for (Rel relation : List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT)) {
                    for (int at = 0; at < 2; at++) {
                        check(program, constant, relation, at);
                    }
                }
            }
        }
    }

    private static void check(Program program, int constant, Rel relation, int at) {
        List<Term<String>> terms = List.of(term("a", program.first()), term("b", program.second()));
        Leaves said = WhatARelationLeavesUndivided.leavesOf(terms, at, ExactRatio.of(constant),
                relation, String::equals, (one, other) -> true, Granularity.DISCRETE,
                BigInteger.valueOf(GREATEST), List.of(),
                new Operations(program.sums(), program.exact()));
        String where = program.name() + ", constant " + constant + " " + relation + " 0, term "
                + at + ": " + said;
        // Each value of the term at `at`, the outcomes of the rows at it that get past the
        // operations — all of them where the program tells every operation, and where it does not,
        // only those the told ones stop.
        for (int value = LEAST; value <= GREATEST; value++) {
            boolean sawTrue = false;
            boolean sawFalse = false;
            for (int other = LEAST; other <= GREATEST; other++) {
                int a = at == 0 ? value : other;
                int b = at == 0 ? other : value;
                if (!getsPast(program, a, b)) {
                    continue;
                }
                if (holds(relation, program.first() * a + program.second() * b + constant)) {
                    sawTrue = true;
                } else {
                    sawFalse = true;
                }
            }
            if (said instanceof Leaves.Undivided && program.exact()) {
                assertTrue(!(sawTrue || sawFalse) || (sawTrue && sawFalse),
                        "undivided, yet only one side has a row at " + value + ": " + where);
            }
            if (said instanceof Leaves.Settled settled) {
                for (SettledRun each : settled.runs()) {
                    if (contains(each, value)) {
                        assertTrue(each.holds() ? !sawFalse : !sawTrue,
                                "settled " + each.holds() + " at " + value
                                        + ", yet a row that gets past the operations breaks it: "
                                        + where);
                    }
                }
            }
        }
    }

    private static boolean getsPast(Program program, int a, int b) {
        for (IntSum each : program.sums()) {
            Map<Object, ExactRatio> values = new LinkedHashMap<>();
            values.put("a", ExactRatio.of(a));
            values.put("b", ExactRatio.of(b));
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
