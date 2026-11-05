package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Statements of one form leave a point of the line exactly where some value of the form is on the
 * right side of every one of them, and taken in one at a time they are told apart from what came
 * before as that is, whatever order they come in.
 */
class FormsHeldTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("y"));

    /**
     * A statement as {@code weight * term + constant} against nought, with the form it is and the
     * quarters from -40 to 40 it holds at, each at its distance from -40.
     */
    private record Written(NumericTerm term, long weight, long constant, Rel rel,
                           TakenConstraint.Affine affine, BitSet holdsAt) {

        Written(NumericTerm term, long weight, long constant, Rel rel) {
            this(term, weight, constant, rel, new TakenConstraint.Affine(new LinearForm<>(
                    ExactRatio.of(constant), Map.of(term, ExactRatio.of(weight))), rel),
                    quartersHeldAt(weight, constant, rel));
        }

        private static BitSet quartersHeldAt(long weight, long constant, Rel rel) {
            BitSet out = new BitSet();
            for (int quarters = -40; quarters <= 40; quarters++) {
                if (rel.holds(Long.signum(weight * quarters + constant * 4))) {
                    out.set(quarters + 40);
                }
            }
            return out;
        }

        @Override
        public String toString() {
            return affine.toString();
        }
    }

    private static boolean leavesNoPoint(List<Written> statements) {
        BitSet holdsAll = (BitSet) statements.getFirst().holdsAt().clone();
        for (Written each : statements) {
            holdsAll.and(each.holdsAt());
        }
        return holdsAll.isEmpty();
    }

    private static List<Written> statementsOf(NumericTerm term, long[] weights,
                                              long[] constants) {
        List<Written> all = new ArrayList<>();
        for (long weight : weights) {
            for (long constant : constants) {
                for (Rel rel : Rel.values()) {
                    all.add(new Written(term, weight, constant, rel));
                }
            }
        }
        return all;
    }

    /** Takes {@code sequence} in, in order, and says at which statement the line was left empty,
     *  or -1 where it never was. */
    private static int closedAt(List<Written> sequence) {
        FormsHeld held = FormsHeld.NONE;
        for (int at = 0; at < sequence.size(); at++) {
            switch (held.taking(sequence.get(at).affine())) {
                case FormsHeld.Taken.Held(var forms) -> held = forms;
                case FormsHeld.Taken.NoPointLeft _ -> {
                    return at;
                }
            }
        }
        return -1;
    }

    @Test
    void whatIsTakenInOneAtATimeLeavesWhatEveryValueOfTheFormLeaves() {
        List<Written> all = statementsOf(X, new long[] {1, -2}, new long[] {-2, 0, 3});
        for (Written first : all) {
            for (Written second : all) {
                for (Written third : all) {
                    List<Written> sequence = List.of(first, second, third);
                    int expected = -1;
                    for (int length = 1; length <= sequence.size() && expected < 0; length++) {
                        if (leavesNoPoint(sequence.subList(0, length))) {
                            expected = length - 1;
                        }
                    }
                    assertEquals(expected, closedAt(sequence), sequence::toString);
                }
            }
        }
    }

    @Test
    void fourStatementsOfAFewLevelsAreToldTheSameWay() {
        List<Written> all = statementsOf(X, new long[] {1}, new long[] {-1, 0, 1});
        for (Written first : all) {
            for (Written second : all) {
                for (Written third : all) {
                    for (Written fourth : all) {
                        List<Written> sequence = List.of(first, second, third, fourth);
                        int expected = -1;
                        for (int length = 1; length <= sequence.size() && expected < 0;
                                length++) {
                            if (leavesNoPoint(sequence.subList(0, length))) {
                                expected = length - 1;
                            }
                        }
                        assertEquals(expected, closedAt(sequence), sequence::toString);
                    }
                }
            }
        }
    }

    @Test
    void theSameStatementsAreToldAsWhatDecidesThemAllAtOnceTellsThem() {
        List<Written> all = statementsOf(X, new long[] {1, -2}, new long[] {-2, 0, 3});
        for (Written first : all) {
            for (Written second : all) {
                for (Written third : all) {
                    List<Written> sequence = List.of(first, second, third);
                    boolean closed = closedAt(sequence) >= 0;
                    assertEquals(WhatStatementsOfOneFormDecide.of(
                            sequence.stream().map(Written::affine).toList(), null)
                            .noRowArrives(), closed, sequence::toString);
                }
            }
        }
    }

    private static ExactRatio twoTo(long exponent) {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, exponent, 0);
    }

    /** {@code x + y} times two to {@code twos} and five to {@code fives}. */
    private static Map<NumericTerm, ExactRatio> bothAt(long twos, long fives) {
        ExactRatio weight = new ExactRatio(BigInteger.ONE, BigInteger.ONE, twos, fives);
        return Map.of(X, weight, Y, weight);
    }

    /**
     * {@code x + y} moved to each end of the powers of two and five, and between: each a number
     * times the others, though the number between two ends is past what the arithmetic holds, so
     * a form joins the first of them it is a number the arithmetic holds times, which is not a
     * matter of which of them it is a number times.
     */
    private static final List<Map<NumericTerm, ExactRatio>> AT_THE_ENDS = List.of(
            bothAt(Long.MIN_VALUE, Long.MIN_VALUE), bothAt(Long.MAX_VALUE, Long.MAX_VALUE),
            bothAt(Long.MIN_VALUE, Long.MAX_VALUE), bothAt(Long.MAX_VALUE, Long.MIN_VALUE),
            bothAt(0, 0));

    /**
     * Forms over two terms, each a number times some of the others, of either sign, and not of the
     * rest; two whose weights are past sixty-four bits apart; and {@link #AT_THE_ENDS}. Each list
     * is of forms a number times each other, and there are more lists than the groups told
     * against one by one, so that a sequence of them is filed by its forms.
     */
    private static final List<List<Map<NumericTerm, ExactRatio>>> FORMS = forms();

    private static List<List<Map<NumericTerm, ExactRatio>>> forms() {
        List<List<Map<NumericTerm, ExactRatio>>> out = new ArrayList<>(List.of(
                List.of(Map.of(X, ExactRatio.of(-3)), Map.of(X, ExactRatio.of(1))),
                List.of(Map.of(X, twoTo(Long.MAX_VALUE), Y, twoTo(Long.MIN_VALUE)),
                        Map.of(X, twoTo(Long.MAX_VALUE).negated(),
                                Y, twoTo(Long.MIN_VALUE).negated())),
                AT_THE_ENDS));
        for (long weight = -12; weight <= 12; weight++) {
            if (weight != 0) {
                out.add(List.of(Map.of(X, ExactRatio.of(1), Y, ExactRatio.of(weight)),
                        Map.of(X, ExactRatio.of(-2), Y, ExactRatio.of(-2 * weight)),
                        Map.of(X, ExactRatio.of(3), Y, ExactRatio.of(3 * weight))));
            }
        }
        return List.copyOf(out);
    }

    private static TakenConstraint.Affine anyStatementOf(List<Map<NumericTerm, ExactRatio>> forms,
                                                         Random random) {
        long[] constants = {-2, 0, 1, 3};
        List<Rel> rels = List.of(Rel.values());
        return new TakenConstraint.Affine(new LinearForm<>(
                ExactRatio.of(constants[random.nextInt(constants.length)]),
                forms.get(random.nextInt(forms.size()))),
                rels.get(random.nextInt(rels.size())));
    }

    /**
     * A statement joins the first group, in the order they were made, of a form it is a number
     * the arithmetic holds times, and leaves no point of the line exactly where the statements of
     * that group taken in alone and it leave none — the group the walk over every group before it
     * finds, whichever forms came before and in whichever order. Each sequence opens with one
     * statement of each of some lists of forms, which leave a point each, so that it goes on past
     * as many groups as were opened.
     */
    @Test
    void aStatementIsToldAgainstTheStatementsBeforeItOfItsFormAndNoOthers() {
        Random random = new Random(3024);
        for (int round = 0; round < 300; round++) {
            List<Integer> forms = new ArrayList<>();
            for (int form = 0; form < FORMS.size(); form++) {
                forms.add(form);
            }
            Collections.shuffle(forms, random);
            forms = new ArrayList<>(forms.subList(0, random.nextInt(forms.size() + 1)));
            for (int length = forms.size() + 1 + random.nextInt(12); forms.size() < length; ) {
                forms.add(random.nextInt(FORMS.size()));
            }
            List<TakenConstraint.Affine> sequence = new ArrayList<>();
            for (int form : forms) {
                sequence.add(anyStatementOf(FORMS.get(form), random));
            }
            // Each group the walk over every group finds, and what its statements alone come to.
            List<TakenConstraint.Affine> firsts = new ArrayList<>();
            List<FormsHeld> alone = new ArrayList<>();
            FormsHeld held = FormsHeld.NONE;
            for (int at = 0; at < sequence.size(); at++) {
                TakenConstraint.Affine added = sequence.get(at);
                int group = 0;
                while (group < firsts.size() && WhatStatementsOfOneFormDecide.factorBetween(
                        firsts.get(group).form().coefs(), added.form().coefs()) == null) {
                    group++;
                }
                if (group == firsts.size()) {
                    firsts.add(added);
                    alone.add(FormsHeld.NONE);
                }
                FormsHeld.Taken expected = alone.get(group).taking(added);
                FormsHeld.Taken taken = held.taking(added);
                if (expected instanceof FormsHeld.Taken.NoPointLeft(var statements)) {
                    assertEquals(statements, assertInstanceOf(FormsHeld.Taken.NoPointLeft.class,
                            taken, sequence::toString).statements(), sequence::toString);
                    break;
                }
                alone.set(group, ((FormsHeld.Taken.Held) expected).forms());
                held = assertInstanceOf(FormsHeld.Taken.Held.class, taken,
                        sequence::toString).forms();
            }
        }
    }

    /**
     * Past the groups told against one by one, a statement is told against the groups of its form
     * up to a factor and no others: none where no group is of its form, and no more than four
     * where its form is a number times theirs past what the arithmetic holds — the four ends of
     * {@link #AT_THE_ENDS}, opened first so that each is a group of its own.
     */
    @Test
    void pastTheGroupsToldOneByOneAStatementIsToldAgainstTheGroupsOfItsFormAlone() {
        List<Map<NumericTerm, ExactRatio>> opened = new ArrayList<>(AT_THE_ENDS);
        for (long weight = 2; weight <= 40; weight++) {
            opened.add(Map.of(X, ExactRatio.of(1), Y, ExactRatio.of(weight)));
        }
        List<Map<NumericTerm, ExactRatio>> asked = new ArrayList<>(opened);
        for (long weight = 41; weight <= 80; weight++) {
            asked.add(Map.of(X, ExactRatio.of(-2), Y, ExactRatio.of(-2 * weight)));
        }
        long[] counting = {0};
        FormsHeld.COUNTING_TOLD = counting;
        try {
            FormsHeld held = FormsHeld.NONE;
            for (Map<NumericTerm, ExactRatio> each : opened) {
                held = ((FormsHeld.Taken.Held) held.taking(nought(each))).forms();
            }
            for (Map<NumericTerm, ExactRatio> each : asked) {
                long before = counting[0];
                held = assertInstanceOf(FormsHeld.Taken.Held.class,
                        held.taking(nought(each))).forms();
                long told = counting[0] - before;
                assertTrue(told <= 4, () -> each + " was told against " + told + " groups");
            }
            assertTrue(counting[0] > 0, "the groups told against are counted");
        } finally {
            FormsHeld.COUNTING_TOLD = null;
        }
    }

    /** {@code form >= 0}, which holds beside any other such statement at nought. */
    private static TakenConstraint.Affine nought(Map<NumericTerm, ExactRatio> form) {
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.ZERO, form), Rel.GE);
    }

    @Test
    void statementsOfAnotherFormAreHeldApartAndTheStatementsOfTheFormLeftAreSaid() {
        FormsHeld held = FormsHeld.NONE;
        held = assertInstanceOf(FormsHeld.Taken.Held.class,
                held.taking(new Written(X, 1, 0, Rel.LE).affine())).forms();
        held = assertInstanceOf(FormsHeld.Taken.Held.class,
                held.taking(new Written(Y, 1, -5, Rel.GE).affine())).forms();

        FormsHeld.Taken closed = held.taking(new Written(X, 1, 0, Rel.GT).affine());

        FormsHeld.Taken.NoPointLeft none = assertInstanceOf(FormsHeld.Taken.NoPointLeft.class,
                closed);
        assertEquals(2, none.statements().size(), "only the statements of x are said");
    }

    @Test
    void aTermInsideAContainerIsLeftOutBecauseEachStatementMayBeOfAnotherElement() {
        NumericTerm element = new NumericTerm.ValueOf(TermPath.of("xs").element());
        FormsHeld held = FormsHeld.NONE;
        held = assertInstanceOf(FormsHeld.Taken.Held.class,
                held.taking(new Written(element, 1, 0, Rel.LE).affine())).forms();

        assertTrue(held.taking(new Written(element, 1, 0, Rel.GT).affine())
                instanceof FormsHeld.Taken.Held);
    }
}
