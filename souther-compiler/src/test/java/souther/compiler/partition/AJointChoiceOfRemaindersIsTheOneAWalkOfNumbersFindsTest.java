package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some statements of remainders by one divisor, moved by a number that lies from nought up to
 * {@code days}, are met by some whole numbers exactly where {@link JointResidues} gives a choice
 * that needs the number no further than {@code days}. Worked out by trying every whole number the
 * form and the number can be, for each bound the number may lie up to.
 */
class AJointChoiceOfRemaindersIsTheOneAWalkOfNumbersFindsTest {

    private static final int[] DIVISORS = {2, 3, 4, 5, 7};

    @Test
    void aChoiceIsGivenExactlyWhereSomeWholeNumbersMeetEveryStatement() {
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
                statements.add(new JointResidues.Statement(random.nextInt(divisor),
                        random.nextInt(3) == 0 ? 0 : 1 + random.nextInt(2), allowed));
            }
            Optional<JointResidues.Choice> choice = JointResidues.least(divisor, statements);
            for (int days = 0; days <= 2 * divisor; days++) {
                boolean some = someWholeNumbersMeetEvery(divisor, statements, days);
                boolean given = choice.isPresent() && choice.get().least() <= days;
                assertEquals(some, given, divisor + " " + statements + " days " + days);
            }
            if (choice.isPresent()) {
                met++;
            } else {
                none++;
            }
        }
        // Both answers are met, or the test says nothing of the one that is not.
        assertTrue(met > 1000 && none > 1000, met + " met, " + none + " none");
    }

    private static boolean someWholeNumbersMeetEvery(int divisor,
                                                     List<JointResidues.Statement> statements,
                                                     int days) {
        // The form is any whole number, and the number any from nought to days.
        for (int form = -3 * divisor; form <= 3 * divisor; form++) {
            for (int n = 0; n <= days; n++) {
                boolean every = true;
                for (JointResidues.Statement each : statements) {
                    every &= each.allowed().contains(Math.floorMod(
                            form + each.onTheNumber() * n + each.shift(), divisor));
                }
                if (every) {
                    return true;
                }
            }
        }
        return false;
    }
}
