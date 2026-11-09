package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules prove written over the positions their equalities leave free is proved of the
 * rules, and the answers about what the rules leave — the ranges, the certificate, whether
 * anything is left — are the rules' own whether or not that was asked.
 *
 * <p>Held over small systems of whole numbers, each rule over up to three of four positions, with
 * the goals asked of them: a goal the domain proves is held against every whole-number point of a
 * box the rules admit, so a proof the equalities should not have given is a point that breaks the
 * goal. A box is not the unbounded space, so this finds a wrong proof and never shows there is
 * none; what shows that is the reduced rules following from the rules, which {@link ReducedRules}
 * is written from.
 */
class WhatTheRulesProveOverThePositionsTheirEqualitiesLeaveFreeIsSoundAndTouchesNothingElseTest {

    private static final int ATOMS = 4;
    private static final int BOX = 6;
    private static final String[] NAMES = {"a", "b", "c", "d"};

    private record Term(int atom, int coef) {}

    private record Row(List<Term> terms, int constant, Rel rel) {}

    private static Row random(Random random, int most, boolean equality) {
        List<Integer> chosen = new ArrayList<>(List.of(0, 1, 2, 3));
        Collections.shuffle(chosen, random);
        List<Term> terms = new ArrayList<>();
        for (int i = 0, size = 1 + random.nextInt(most); i < size; i++) {
            int coef = random.nextInt(5) - 2;
            terms.add(new Term(chosen.get(i), coef == 0 ? 1 : coef));
        }
        return new Row(terms, random.nextInt(9) - 4,
                equality ? Rel.EQ : random.nextBoolean() ? Rel.LE : Rel.GE);
    }

    private static LinearForm<String> form(Row row) {
        return form(row, NAMES);
    }

    /** {@code row} with its positions called {@code names}. */
    private static LinearForm<String> form(Row row, String[] names) {
        LinearForm<String> out = LinearForm.constant(ExactRatio.of(row.constant()));
        for (Term t : row.terms()) {
            out = out.plus(LinearForm.<String>atom(names[t.atom()])
                    .times(ExactRatio.of(t.coef())).orNull()).orNull();
        }
        return out;
    }

    private static NumericDomain<String> domain(List<Row> rules) {
        return domain(rules, NAMES);
    }

    private static NumericDomain<String> domain(List<Row> rules, String[] names) {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (String each : names) {
            spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        NumericDomain<String> out = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        for (Row rule : rules) {
            out = out.assume(form(rule, names), rule.rel(), spaces);
        }
        return out;
    }

    private static boolean holds(Row row, int[] at) {
        long sum = row.constant();
        for (Term t : row.terms()) {
            sum += (long) t.coef() * at[t.atom()];
        }
        return switch (row.rel()) {
            case GE -> sum >= 0;
            case LE -> sum <= 0;
            default -> sum == 0;
        };
    }

    /** Whether {@code at} satisfies every rule; a loop, since this is asked of every point of the box. */
    private static boolean everyRuleHolds(List<Row> rules, int[] at) {
        for (Row rule : rules) {
            if (!holds(rule, at)) {
                return false;
            }
        }
        return true;
    }

    /** Whether some point of the box satisfies every rule and breaks the goal. */
    private static boolean breaks(List<Row> rules, Row goal) {
        int[] at = new int[ATOMS];
        for (at[0] = -BOX; at[0] <= BOX; at[0]++) {
            for (at[1] = -BOX; at[1] <= BOX; at[1]++) {
                for (at[2] = -BOX; at[2] <= BOX; at[2]++) {
                    for (at[3] = -BOX; at[3] <= BOX; at[3]++) {
                        if (!holds(goal, at) && everyRuleHolds(rules, at)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    private static List<Row> system(Random random) {
        List<Row> rules = new ArrayList<>();
        for (int i = 0; i < 2; i++) {
            rules.add(random(random, 3, true));
        }
        for (int i = 0; i < 3; i++) {
            rules.add(random(random, 3, false));
        }
        return rules;
    }

    /** A goal proved of the rules is one no point of the box breaks. */
    @Test
    void whatIsProvedIsBrokenByNoPointOfTheBox() {
        Random random = new Random(11);
        int proved = 0;
        List<String> wrong = new ArrayList<>();
        for (int round = 0; round < 120; round++) {
            List<Row> rules = system(random);
            NumericDomain<String> domain = domain(rules);
            for (int i = 0; i < 10; i++) {
                Row goal = random(random, 3, false);
                if (domain.entails(form(goal), goal.rel())) {
                    proved++;
                    if (breaks(rules, goal)) {
                        wrong.add(rules + " proves " + goal);
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
        assertTrue(proved > 0, "nothing was proved, so nothing was held to the box");
    }

    /**
     * What the rules leave a position, the certificate, whether anything is left and what the
     * ranges and the closed differences prove are the same before and after the rules were asked
     * a goal the reduced rules answer.
     */
    @Test
    void askingAGoalLeavesWhatTheRulesLeaveAsItWas() {
        Random random = new Random(13);
        for (int round = 0; round < 150; round++) {
            List<Row> rules = system(random);
            NumericDomain<String> asked = domain(rules);
            NumericDomain<String> untouched = domain(rules);
            for (int i = 0; i < 10; i++) {
                Row goal = random(random, 3, false);
                asked.entails(form(goal), goal.rel());
            }
            assertEquals(untouched.isBottom(), asked.isBottom(), rules.toString());
            assertEquals(untouched.projectionCertification(), asked.projectionCertification(),
                    rules.toString());
            for (String atom : NAMES) {
                assertEquals(untouched.boundsOf(atom), asked.boundsOf(atom), rules.toString());
            }
            for (int i = 0; i < 10; i++) {
                Row goal = random(random, 3, false);
                assertEquals(untouched.provenByTheBoxAndItsDifferences(form(goal), goal.rel()),
                        asked.provenByTheBoxAndItsDifferences(form(goal), goal.rel()),
                        rules + " " + goal);
            }
        }
    }

    /**
     * What a system proves does not depend on what its positions are called: a position is solved
     * for by how the rules use it, and the names decide only between positions used alike.
     */
    @Test
    void whatIsProvedDoesNotDependOnWhatThePositionsAreCalled() {
        Random random = new Random(19);
        List<String> moved = new ArrayList<>();
        for (int round = 0; round < 250; round++) {
            List<Row> rules = system(random);
            NumericDomain<String> plain = domain(rules);
            if (plain.isBottom()) {
                continue;
            }
            List<Row> goals = new ArrayList<>();
            for (int i = 0; i < 10; i++) {
                goals.add(random(random, 3, false));
            }
            for (int variant = 0; variant < 3; variant++) {
                List<Integer> shuffled = new ArrayList<>(List.of(0, 1, 2, 3));
                Collections.shuffle(shuffled, random);
                String[] renamed = new String[ATOMS];
                for (int i = 0; i < ATOMS; i++) {
                    renamed[i] = "n" + shuffled.get(i);
                }
                NumericDomain<String> other = domain(rules, renamed);
                for (Row goal : goals) {
                    if (plain.entails(form(goal), goal.rel())
                            != other.entails(form(goal, renamed), goal.rel())) {
                        moved.add(rules + " " + goal + " as " + String.join(",", renamed));
                    }
                }
            }
        }
        assertEquals(List.of(), moved);
    }

    /** The equalities said in another order are the same equalities, and are solved the same. */
    @Test
    void theOrderTheEqualitiesAreSaidInDoesNotChangeWhatTheyAreSolvedTo() {
        Random random = new Random(17);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        for (int round = 0; round < 200; round++) {
            List<AffineConstraint<String>> equalities = new ArrayList<>();
            for (int i = 0, count = 1 + random.nextInt(3); i < count; i++) {
                Row row = random(random, 3, true);
                if (domain(List.of(row)).rulesRead().isEmpty()) {
                    continue;
                }
                equalities.addAll(domain(List.of(row)).rulesRead());
            }
            ReducedRules<String> one = ReducedRules.of(equalities, order);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(equalities);
            Collections.shuffle(shuffled, random);
            ReducedRules<String> other = ReducedRules.of(shuffled, order);
            assertEquals(one == null, other == null, equalities.toString());
            if (one == null) {
                continue;
            }
            assertEquals(one.contradicted(), other.contradicted(), equalities.toString());
            if (one.contradicted()) {
                continue;   // what nothing satisfies has no one way of being written
            }
            for (int i = 0; i < 8; i++) {
                Row goal = random(random, 3, false);
                Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                for (Term t : goal.terms()) {
                    coefs.put(NAMES[t.atom()], ExactRatio.of(t.coef()));
                }
                ReducedRules.Goal<String> asked =
                        new ReducedRules.Goal<>(coefs, ExactRatio.of(goal.constant()));
                assertEquals(one.put(asked), other.put(asked), equalities.toString());
            }
        }
    }
}
