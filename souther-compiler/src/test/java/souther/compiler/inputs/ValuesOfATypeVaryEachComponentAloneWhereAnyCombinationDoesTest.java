package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values made of a record vary each component alone wherever some combination of the others
 * lets them, however far that combination is from the first values of the others.
 *
 * <p>What the values are asked for is that an order reading a record is held to each component, so a
 * component no two values differ in alone is one nothing asks about — and the maker refuses it
 * rather than passing over it. That refusal is a claim about the record, and is made only where
 * every combination of the others was asked: where the values nearest the first ones hold no such
 * pair, the asking goes on rather than stopping at the claim.
 */
class ValuesOfATypeVaryEachComponentAloneWhereAnyCombinationDoesTest {

    /**
     * Three flags a constructor ties together: two may differ only where the third is set, and all
     * three are not set at once.
     *
     * <p>Beside the first values — every flag clear — moving one other flag gives no value in which
     * the first or the second is set alone, and every pair varying either of them differs from the
     * first values in two flags: {@code 001} and {@code 101} vary the first, {@code 001} and
     * {@code 011} the second.
     */
    record Flags(boolean a, boolean b, boolean c) {

        Flags {
            if ((a != b && !c) || (a && b && c)) {
                throw new IllegalArgumentException("two flags differ only where the third is set");
            }
        }
    }

    @Test
    void aComponentVariedAloneOnlyFarFromTheFirstValuesIsVariedAlone() {
        List<Object> made = new ValuesOfAType().of(Flags.class);

        assertTrue(made.contains(new Flags(false, false, true))
                        && made.contains(new Flags(true, false, true)),
                () -> "the first flag varied alone: " + made);
        assertTrue(made.contains(new Flags(false, false, true))
                        && made.contains(new Flags(false, true, true)),
                () -> "the second flag varied alone: " + made);
    }
}
