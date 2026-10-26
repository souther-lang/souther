package souther.compiler.reading;

import souther.compiler.coverage.Numberings;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.HashSet;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The combinations of arms of several forks do not fall into as many buckets as the parts taken
 * add up to.
 *
 * <p>The arms of one fork differ in their part number alone, and a set of decisions hashes to the
 * sum of its members. Hashed as the fields are, taking part 1 of one fork and part 0 of another
 * summed to what part 0 of the first and part 1 of the second did, so a group of forks had as many
 * hashes as there are sums of parts.
 */
class TheArmsOfSeveralForksHashApartTest {

    private static final int FORKS = 4;
    private static final int PARTS = 3;

    private static Condition arm(int fork, int part) {
        SourceConstructOrigin origin = new SourceConstructOrigin(
                new WrittenOwner.Body("fixture", "b"), fork, 0, SourceConstruct.IF);
        return new Condition.Arm(Numberings.arm(origin, part), Optional.empty());
    }

    @Test
    void everyChoiceOfAPartForEachForkHashesToItsOwn() {
        Set<Integer> hashes = new HashSet<>();
        int choices = 1;
        for (int fork = 0; fork < FORKS; fork++) {
            choices *= PARTS;
        }
        for (int choice = 0; choice < choices; choice++) {
            Set<Condition> taken = new HashSet<>();
            int left = choice;
            for (int fork = 0; fork < FORKS; fork++) {
                taken.add(arm(fork, left % PARTS));
                left /= PARTS;
            }
            hashes.add(taken.hashCode());
        }

        assertEquals(choices, hashes.size(),
                "a hash for each choice, where the sums of the parts are few");
    }
}
