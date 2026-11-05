package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
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

    /** A statement as {@code weight * term + constant} against nought. */
    private record Written(NumericTerm term, long weight, long constant, Rel rel) {

        TakenConstraint.Affine affine() {
            return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant),
                    Map.of(term, ExactRatio.of(weight))), rel);
        }

        boolean holdsAt(int quarters) {
            return rel.holds(Long.signum(weight * quarters + constant * 4));
        }
    }

    private static boolean leavesNoPoint(List<Written> statements) {
        for (int quarters = -40; quarters <= 40; quarters++) {
            boolean holdsAll = true;
            for (Written each : statements) {
                holdsAll &= each.holdsAt(quarters);
            }
            if (holdsAll) {
                return false;
            }
        }
        return true;
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
                    assertEquals(expected, closedAt(sequence), sequence.toString());
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
                        assertEquals(expected, closedAt(sequence), sequence.toString());
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
                            .noRowArrives(), closed, sequence.toString());
                }
            }
        }
    }

    private static ExactRatio twoTo(long exponent) {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, exponent, 0);
    }

    /**
     * Forms over two terms, each a number times some of the others, of either sign, and not of the
     * rest; and two whose weights the arithmetic cannot divide one by the other. Each list is the
     * forms one of the others is a number times, and there are more of them than the groups told
     * against one by one, so that a sequence of them is filed by its forms.
     */
    private static final List<List<Map<NumericTerm, ExactRatio>>> FORMS = forms();

    private static List<List<Map<NumericTerm, ExactRatio>>> forms() {
        List<List<Map<NumericTerm, ExactRatio>>> out = new ArrayList<>(List.of(
                List.of(Map.of(X, ExactRatio.of(-3)), Map.of(X, ExactRatio.of(1))),
                List.of(Map.of(X, twoTo(Long.MAX_VALUE), Y, twoTo(Long.MIN_VALUE)),
                        Map.of(X, twoTo(Long.MAX_VALUE).negated(),
                                Y, twoTo(Long.MIN_VALUE).negated()))));
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
        return new TakenConstraint.Affine(new LinearForm<>(
                ExactRatio.of(constants[random.nextInt(constants.length)]),
                forms.get(random.nextInt(forms.size()))),
                Rel.values()[random.nextInt(Rel.values().length)]);
    }

    /**
     * A statement joins the statements before it of a form it is a number times, and leaves no
     * point of the line exactly where those and it leave none — whichever forms came before, in
     * whichever order, so that finding the statements of its form among the others is the walk
     * over every one of them. Each sequence opens with one statement of each of some forms, which
     * leave a point each, so that it goes on past as many groups as were opened.
     */
    @Test
    void aStatementIsToldAgainstTheStatementsBeforeItOfItsFormAndNoOthers() {
        Random random = new Random(3024);
        for (int round = 0; round < 3000; round++) {
            List<List<Map<NumericTerm, ExactRatio>>> opened = new ArrayList<>(FORMS);
            Collections.shuffle(opened, random);
            List<TakenConstraint.Affine> sequence = new ArrayList<>();
            for (List<Map<NumericTerm, ExactRatio>> each
                    : opened.subList(0, random.nextInt(opened.size() + 1))) {
                sequence.add(anyStatementOf(each, random));
            }
            for (int length = sequence.size() + 1 + random.nextInt(12);
                    sequence.size() < length; ) {
                sequence.add(anyStatementOf(FORMS.get(random.nextInt(FORMS.size())), random));
            }
            FormsHeld held = FormsHeld.NONE;
            for (int at = 0; at < sequence.size(); at++) {
                TakenConstraint.Affine added = sequence.get(at);
                List<TakenConstraint.Affine> ofItsForm = new ArrayList<>();
                for (TakenConstraint.Affine each : sequence.subList(0, at + 1)) {
                    if (WhatStatementsOfOneFormDecide.factorBetween(
                            each.form().coefs(), added.form().coefs()) != null) {
                        ofItsForm.add(each);
                    }
                }
                boolean none = WhatStatementsOfOneFormDecide.of(ofItsForm, null).noRowArrives();
                FormsHeld.Taken taken = held.taking(added);
                if (none) {
                    assertEquals(ofItsForm, assertInstanceOf(FormsHeld.Taken.NoPointLeft.class,
                            taken, sequence.toString()).statements(), sequence.toString());
                    break;
                }
                held = assertInstanceOf(FormsHeld.Taken.Held.class, taken,
                        sequence.toString()).forms();
            }
        }
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
