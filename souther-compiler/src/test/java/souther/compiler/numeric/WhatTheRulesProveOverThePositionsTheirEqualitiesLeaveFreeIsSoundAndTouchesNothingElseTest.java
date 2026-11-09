package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

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
        return domain(rules, names, Granularity.DISCRETE, Granularity.DISCRETE);
    }

    /** The first two positions spaced as {@code first}, the other two as {@code second}. */
    private static NumericDomain<String> domain(List<Row> rules, String[] names, Granularity first,
                                                Granularity second) {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (int i = 0; i < names.length; i++) {
            spaces.put(names[i], NumberSpace.spacedOnly(i < 2 ? first : second));
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

    /** {@code row} at {@code halves}, each position given in halves: a sum of halves twice over. */
    private static boolean holdsInHalves(Row row, int[] halves) {
        long sum = 2L * row.constant();
        for (Term t : row.terms()) {
            sum += (long) t.coef() * halves[t.atom()];
        }
        return switch (row.rel()) {
            case GE -> sum >= 0;
            case LE -> sum <= 0;
            default -> sum == 0;
        };
    }

    /**
     * Whether some point breaks the goal and satisfies every rule where the first two positions are
     * whole numbers and the other two are halves of them: a point of what a decimal can be, so a
     * point found here is a real counterexample and none found says only that this did not find one.
     */
    private static boolean breaksWholeAndHalves(List<Row> rules, Row goal) {
        int[] at = new int[ATOMS];
        for (at[0] = -BOX; at[0] <= BOX; at[0] += 2) {
            for (at[1] = -BOX; at[1] <= BOX; at[1] += 2) {
                for (at[2] = -BOX; at[2] <= BOX; at[2]++) {
                    for (at[3] = -BOX; at[3] <= BOX; at[3]++) {
                        if (!holdsInHalves(goal, at) && everyRuleHoldsInHalves(rules, at)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    private static boolean everyRuleHoldsInHalves(List<Row> rules, int[] halves) {
        for (Row rule : rules) {
            if (!holdsInHalves(rule, halves)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Over whole numbers and decimals together a weight that is a fraction comes of solving for a
     * position, and what the positions solved for carried is not kept; none of it makes a goal
     * proved that a whole-number-and-half point breaks.
     */
    @Test
    void whatIsProvedOverWholeNumbersAndDecimalsIsBrokenByNoPointOfTheHalves() {
        Random random = new Random(23);
        int proved = 0;
        List<String> wrong = new ArrayList<>();
        for (int round = 0; round < 120; round++) {
            List<Row> rules = system(random);
            NumericDomain<String> domain =
                    domain(rules, NAMES, Granularity.DISCRETE, Granularity.DENSE);
            for (int i = 0; i < 10; i++) {
                Row goal = random(random, 3, false);
                if (domain.entails(form(goal), goal.rel())) {
                    proved++;
                    if (breaksWholeAndHalves(rules, goal)) {
                        wrong.add(rules + " proves " + goal);
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
        assertTrue(proved > 0, "nothing was proved, so nothing was held to the points");
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
        assertEquals(List.of(), movedByRenaming(random, 250, () -> system(random)));
    }

    /** A rule over the two positions beside the four, which none of the goals names. */
    private static Row beside(Random random, boolean equality) {
        List<Term> terms = new ArrayList<>();
        for (int i = 0, size = 1 + random.nextInt(2); i < size; i++) {
            int coef = random.nextInt(5) - 2;
            terms.add(new Term(ATOMS + i, coef == 0 ? 1 : coef));
        }
        return new Row(terms, random.nextInt(9) - 4,
                equality ? Rel.EQ : random.nextBoolean() ? Rel.LE : Rel.GE);
    }

    /**
     * What is proved of rules is still proved beside rules over positions neither the goal nor
     * those rules name. Held over the small systems this class asks, which are far from every
     * bound a reading is limited by: past one of them a proof may be left unread, and for every
     * naming alike.
     */
    @Test
    void whatIsProvedIsStillProvedBesideRulesOverOtherPositions() {
        Random random = new Random(37);
        String[] withTheOthers = {"a", "b", "c", "d", "e", "f"};
        List<String> lost = new ArrayList<>();
        int proved = 0;
        for (int round = 0; round < 150; round++) {
            List<Row> rules = system(random);
            List<Row> beside = new ArrayList<>(rules);
            beside.add(beside(random, true));
            beside.add(beside(random, true));
            beside.add(beside(random, false));
            NumericDomain<String> alone = domain(rules);
            NumericDomain<String> together = domain(beside, withTheOthers);
            for (int i = 0; i < 10; i++) {
                Row goal = random(random, 3, false);
                if (alone.entails(form(goal), goal.rel())) {
                    proved++;
                    if (!together.entails(form(goal, withTheOthers), goal.rel())) {
                        lost.add(rules + " proves " + goal + " and not beside " + beside);
                    }
                }
            }
        }
        assertEquals(List.of(), lost);
        assertTrue(proved > 0, "nothing was proved, so nothing was held beside the others");
    }

    /**
     * The same where the rules are unchanged by exchanging two positions: nothing in the rules
     * tells the two apart, so the names would decide which one an equality is solved for, and a
     * goal written over what is left was proved in one writing and not in the other.
     */
    @Test
    void whatIsProvedDoesNotDependOnWhatTwoInterchangeablePositionsAreCalled() {
        Random random = new Random(29);
        assertEquals(List.of(), movedByRenaming(random, 150, () -> symmetric(random)));
    }

    /**
     * {@code a + b = 4} with {@code d} at least each of them and {@code 2d + 2a + c + 1 <= 0} and
     * the same of {@code b}: unchanged by exchanging {@code a} and {@code b}. Solved for {@code a}
     * or for {@code b} by their names, the goal over what is left was proved in one writing and
     * not in the other.
     */
    @Test
    void aSystemUnchangedByExchangingTwoPositionsIsAnsweredTheSameWhateverTheyAreCalled() {
        List<Row> rules = List.of(
                new Row(List.of(new Term(1, 1), new Term(0, 1)), -4, Rel.EQ),
                new Row(List.of(new Term(1, -1), new Term(3, 1)), 0, Rel.GE),
                new Row(List.of(new Term(3, 2), new Term(0, 2), new Term(2, 1)), 1, Rel.LE),
                new Row(List.of(new Term(0, 1), new Term(1, 1)), -4, Rel.EQ),
                new Row(List.of(new Term(0, -1), new Term(3, 1)), 0, Rel.GE),
                new Row(List.of(new Term(3, 2), new Term(1, 2), new Term(2, 1)), 1, Rel.LE));
        Row goal = new Row(List.of(new Term(2, -2), new Term(0, 2), new Term(3, -2)), -3, Rel.GE);
        String[] renamed = {"n2", "n1", "n3", "n0"};

        assertEquals(domain(rules).entails(form(goal), goal.rel()),
                domain(rules, renamed).entails(form(goal, renamed), goal.rel()));
    }

    /** A system and its image with positions {@code a} and {@code b} exchanged. */
    private static List<Row> symmetric(Random random) {
        List<Row> rules = new ArrayList<>();
        rules.add(random(random, 3, true));
        for (int i = 0; i < 2; i++) {
            rules.add(random(random, 3, false));
        }
        for (Row each : List.copyOf(rules)) {
            List<Term> exchanged = new ArrayList<>();
            for (Term term : each.terms()) {
                exchanged.add(new Term(term.atom() < 2 ? 1 - term.atom() : term.atom(), term.coef()));
            }
            rules.add(new Row(exchanged, each.constant(), each.rel()));
        }
        return rules;
    }

    /** What was asked that was answered differently once the positions were called other things. */
    private static List<String> movedByRenaming(Random random, int rounds,
                                                Supplier<List<Row>> systems) {
        List<String> moved = new ArrayList<>();
        for (int round = 0; round < rounds; round++) {
            List<Row> rules = systems.get();
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
        return moved;
    }

    /**
     * The rules said in another order, and an equality written the other way round ({@code x = 3}
     * as {@code -x = -3}, which are one equality), are solved the same: the same rules over the
     * free positions, and a goal written the same.
     */
    @Test
    void theWayTheRulesAreWrittenDoesNotChangeWhatTheEqualitiesAreSolvedTo() {
        Random random = new Random(17);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        for (int round = 0; round < 300; round++) {
            List<AffineConstraint<String>> rules = domain(system(random)).rulesRead();
            List<ReducedRules<String>> one = ReducedRules.of(rules, order);
            List<AffineConstraint<String>> written = new ArrayList<>();
            for (AffineConstraint<String> each : rules) {
                written.add(each instanceof AffineConstraint.Equality<String> equality
                        && random.nextBoolean()
                        ? new AffineConstraint.Equality<>(equality.form().negated(),
                                equality.at().negated())
                        : each);
            }
            Collections.shuffle(written, random);
            List<ReducedRules<String>> other = ReducedRules.of(written, order);
            assertEquals(one.size(), other.size(), rules.toString());
            if (one.isEmpty()) {
                continue;
            }
            assertEquals(rulesOf(one), rulesOf(other), rules + " written as " + written);
            for (int i = 0; i < 8; i++) {
                Row goal = random(random, 3, false);
                Map<String, ExactRatio> coefs = new LinkedHashMap<>();
                for (Term t : goal.terms()) {
                    coefs.put(NAMES[t.atom()], ExactRatio.of(t.coef()));
                }
                ReducedRules.Goal<String> asked =
                        new ReducedRules.Goal<>(coefs, ExactRatio.of(goal.constant()));
                assertEquals(goalsOf(one, asked), goalsOf(other, asked), rules.toString());
            }
        }
    }

    /** What each reduction says, as a set: the reductions are not in an order. */
    private static Set<Set<ReducedRules.Rule<String>>> rulesOf(List<ReducedRules<String>> each) {
        return each.stream().map(one -> Set.copyOf(one.rules())).collect(Collectors.toSet());
    }

    /** The goal as each reduction writes it, as a set. */
    private static Set<ReducedRules.Goal<String>> goalsOf(List<ReducedRules<String>> each,
                                                         ReducedRules.Goal<String> asked) {
        Set<ReducedRules.Goal<String>> out = new HashSet<>();
        for (ReducedRules<String> one : each) {
            out.add(one.put(asked));
        }
        return out;
    }
}
