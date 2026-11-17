package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some statements of remainders by one divisor, moved by a number that lies from nought up to
 * {@code days}, are met by some whole numbers exactly where {@link JointResidues} gives a choice
 * that needs the number no further than {@code days}; and the choice it gives meets every
 * statement. Worked out by trying every whole number the form and the number can be, for each bound
 * the number may lie up to, in {@link BigInteger} so that what is tried overflows nowhere.
 *
 * <p>The weights and shifts are any {@code int}, the extremes among them: a statement is of a
 * remainder, and what a weight comes to modulo the divisor is what matters, which a sum in
 * {@code int} does not keep.
 */
class AJointChoiceOfRemaindersIsTheOneAWalkOfNumbersFindsTest {

    private static final int[] DIVISORS = {2, 3, 4, 5, 7, 64};

    private static final int[] EXTREMES = {0, 1, 2, -1, -2, Integer.MAX_VALUE, Integer.MIN_VALUE,
            Integer.MAX_VALUE - 1, Integer.MIN_VALUE + 1};

    @Test
    void aChoiceIsGivenExactlyWhereSomeWholeNumbersMeetEveryStatementAndMeetsThem() {
        Random random = new Random(3264);
        int met = 0;
        int none = 0;
        for (int instance = 0; instance < 20000; instance++) {
            int divisor = DIVISORS[random.nextInt(DIVISORS.length)];
            List<JointResidues.Statement> statements = new ArrayList<>();
            for (int i = 1 + random.nextInt(5); i > 0; i--) {
                Set<Integer> allowed = new LinkedHashSet<>();
                for (int r = 0; r < divisor; r++) {
                    if (random.nextInt(3) > 0) {
                        allowed.add(r);
                    }
                }
                if (allowed.isEmpty()) {
                    allowed.add(random.nextInt(divisor));
                }
                statements.add(new JointResidues.Statement(anInt(random), anInt(random), allowed));
            }
            JointResidues.Answer answer = JointResidues.least(divisor, statements);
            if (answer instanceof JointResidues.Choice choice) {
                assertTrue(meetsEvery(divisor, statements, BigInteger.valueOf(choice.x()),
                        BigInteger.valueOf(choice.least())),
                        "the choice meets every statement: " + choice + " " + statements);
            }
            int bound = divisor == 64 ? 2 : 2 * divisor;
            for (int days = 0; days <= bound; days++) {
                boolean some = someWholeNumbersMeetEvery(divisor, statements, days);
                boolean given = answer instanceof JointResidues.Choice choice
                        && choice.least() <= days;
                assertEquals(some, given, divisor + " " + statements + " days " + days);
            }
            if (answer instanceof JointResidues.Choice) {
                met++;
            } else {
                none++;
            }
        }
        // Both answers are met, or the test says nothing of the one that is not.
        assertTrue(met > 1000 && none > 1000, met + " met, " + none + " none");
    }

    /** The number is the least that meets them, where that is past the bounds the sweep above asks
     *  for the largest divisor: {@code x} is held at nought and {@code x + n} at five, so the
     *  number is five and no less. */
    @Test
    void theNumberChosenIsTheLeastEvenWhereTheDivisorIsTheLargestSearched() {
        List<JointResidues.Statement> statements = List.of(
                new JointResidues.Statement(0, 0, Set.of(0)),
                new JointResidues.Statement(0, 1, Set.of(5)));
        assertEquals(new JointResidues.Choice(0, 5),
                JointResidues.least(JointResidues.MOST_DIVISOR, statements));
    }

    /** A divisor past what is searched is no answer that the statements cannot be met, and is not
     *  searched. */
    @Test
    void aDivisorPastWhatIsSearchedIsNotSearchedAndIsNoAnswerOfNone() {
        List<JointResidues.Statement> statements =
                List.of(new JointResidues.Statement(0, 1, Set.of(0)));
        assertEquals(new JointResidues.NotSearched(),
                JointResidues.least(JointResidues.MOST_DIVISOR + 1, statements));
        assertTrue(JointResidues.least(JointResidues.MOST_DIVISOR, statements)
                instanceof JointResidues.Choice);
    }

    private static int anInt(Random random) {
        return switch (random.nextInt(3)) {
            case 0 -> EXTREMES[random.nextInt(EXTREMES.length)];
            case 1 -> random.nextInt();
            default -> random.nextInt(7);
        };
    }

    private static boolean someWholeNumbersMeetEvery(int divisor,
                                                     List<JointResidues.Statement> statements,
                                                     int days) {
        // The form is any whole number, and the number any from nought to days.
        for (int form = -3 * divisor; form <= 3 * divisor; form++) {
            for (int n = 0; n <= days; n++) {
                if (meetsEvery(divisor, statements, BigInteger.valueOf(form),
                        BigInteger.valueOf(n))) {
                    return true;
                }
            }
        }
        return false;
    }

    private static boolean meetsEvery(int divisor, List<JointResidues.Statement> statements,
                                      BigInteger form, BigInteger n) {
        for (JointResidues.Statement each : statements) {
            BigInteger sum = form.add(BigInteger.valueOf(each.onTheNumber()).multiply(n))
                    .add(BigInteger.valueOf(each.shift()));
            if (!each.allowed().contains(sum.mod(BigInteger.valueOf(divisor)).intValueExact())) {
                return false;
            }
        }
        return true;
    }
}
