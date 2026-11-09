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
 * What the rules prove of a goal is still proved when rules are added over positions the goal and
 * its rules do not name: more rules say more, and rules about other positions say nothing about
 * these. Asked of random systems with equalities, so that the ways an equality is solved for and
 * the bounds on how many of them are tried are in play.
 */
class WhatIsProvedIsStillProvedWhenRulesAboutOtherPositionsAreAddedTest {

    private record Term(int atom, int coef) {}

    private record Row(List<Term> terms, int constant, Rel rel) {}

    private static final String[] NAMES = {"a", "b", "c", "d"};
    private static final String[] OTHER = {"e", "f", "g", "h"};

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

    private static LinearForm<String> form(Row row, String[] names) {
        LinearForm<String> out = LinearForm.constant(ExactRatio.of(row.constant()));
        for (Term t : row.terms()) {
            out = out.plus(LinearForm.<String>atom(names[t.atom()])
                    .times(ExactRatio.of(t.coef())).orNull()).orNull();
        }
        return out;
    }

    private static NumericDomain<String> domain(List<Row> rules, List<Row> over) {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (String each : NAMES) {
            spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        for (String each : OTHER) {
            spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        NumericDomain<String> out = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        for (Row rule : rules) {
            out = out.assume(form(rule, NAMES), rule.rel(), spaces);
        }
        for (Row rule : over) {
            out = out.assume(form(rule, OTHER), rule.rel(), spaces);
        }
        return out;
    }

    @Test
    void aProofIsKeptWhenRulesOverOtherPositionsAreAdded() {
        Random random = new Random(7);
        int proved = 0;
        List<String> lost = new ArrayList<>();
        for (int round = 0; round < 3000; round++) {
            List<Row> rules = new ArrayList<>();
            for (int i = 0; i < 2; i++) {
                rules.add(random(random, 3, true));
            }
            for (int i = 0; i < 3; i++) {
                rules.add(random(random, 3, false));
            }
            NumericDomain<String> plain = domain(rules, List.of());
            if (plain.isBottom()) {
                continue;
            }
            List<Row> added = new ArrayList<>();
            for (int i = random.nextInt(4); i > 0; i--) {
                added.add(random(random, 3, true));
            }
            for (int i = random.nextInt(4); i > 0; i--) {
                added.add(random(random, 3, false));
            }
            NumericDomain<String> more = domain(rules, added);
            if (more.isBottom()) {
                continue;
            }
            for (int i = 0; i < 12; i++) {
                Row goal = random(random, 3, false);
                if (plain.entails(form(goal, NAMES), goal.rel())) {
                    proved++;
                    if (!more.entails(form(goal, NAMES), goal.rel())) {
                        lost.add(rules + " with " + added + " no longer proves " + goal);
                    }
                }
            }
        }
        assertEquals(List.of(), lost);
        assertTrue(proved > 0, "nothing was proved, so nothing was held to the added rules");
    }
}
