package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Why a measure has no number is answered by one of three families, and by one of them only.
 *
 * <p>{@link NotApplicableReason}, {@link NotMeasuredReason} and {@link FailureReason} are three
 * sealed interfaces over the same reasons, and every reader that tells them apart does it by asking
 * which one a reason is — a report opens a sentence with {@code not applicable} or
 * {@code not measured} on that answer alone. Asking it is a {@code switch} whose arms are the three,
 * and the arms are tried in the order they are written: a reason in two families is answered by
 * whichever arm comes first, whatever the measurement holding it says it is.
 *
 * <p>Java lets that be written. Two sealed interfaces may permit one type and that type may
 * implement both, and every {@code switch} over either family stays exhaustive — so the compiler
 * has nothing to say and the reader that picks the first arm is right about the code and wrong
 * about the reason. This is the same defect as a reason type standing for two states, one level up:
 * a classification chosen from an axis that does not settle it.
 *
 * <p>So it is asked here, of the families themselves.
 */
class AReasonIsInOneFamilyAndNotTwoTest {

    private static final List<Class<?>> FAMILIES =
            List.of(NotApplicableReason.class, NotMeasuredReason.class, FailureReason.class);

    /** No reason a measure can give is in two of the three. */
    @Test
    void noReasonIsInTwoFamilies() {
        assertEquals(Set.of(), inTwoFamilies(FAMILIES),
                "a reason in two families is given the words of whichever family a reader asks"
                        + " about first");
    }

    /**
     * And the question was put to something.
     *
     * <p>A family whose permitted types could not be walked answers nothing, and a check over
     * nothing passes. What is asserted is that each family stands for reasons at all, which is what
     * the check above is over.
     */
    @Test
    void everyFamilyStandsForSomeReason() {
        for (Class<?> family : FAMILIES) {
            assertTrue(!reasonsIn(family).isEmpty(),
                    family.getSimpleName() + " stands for no reason, so nothing was compared");
        }
    }

    /**
     * And what each family stands for is all of it.
     *
     * <p>The walk ends at the types nothing may extend. A {@code non-sealed} branch anywhere in a
     * family lets a type outside this compilation implement it, and the set walked here is then not
     * the family — a reason could be in two of them and appear in neither walk.
     */
    @Test
    void everyReasonIsATypeNothingElseExtends() {
        for (Class<?> family : FAMILIES) {
            for (Class<?> reason : reasonsIn(family)) {
                assertTrue(Modifier.isFinal(reason.getModifiers()) || reason.isEnum(),
                        reason.getName() + " may be extended from outside, so what "
                                + family.getSimpleName() + " stands for is not enumerable");
            }
        }
    }

    /**
     * And the question finds an overlap where there is one.
     *
     * <p>Two families and a reason in both, written the way Java allows it. Without this the check
     * above passes on a walk that returns nothing, on a comparison that asks the wrong thing, and
     * on any other reason it never reaches the assertion — all of which read as the invariant
     * holding.
     */
    @Test
    void andItSaysSoWhenAReasonIsInTwo() {
        assertEquals(Set.of("BothAtOnce is a OneFamily and a TheOtherFamily"),
                inTwoFamilies(List.of(OneFamily.class, TheOtherFamily.class)));
    }

    sealed interface OneFamily permits BothAtOnce {}

    sealed interface TheOtherFamily permits BothAtOnce {}

    enum BothAtOnce implements OneFamily, TheOtherFamily {
        IT
    }

    /** Each reason that is in two of {@code families}, said once however many walks reach it. */
    private static Set<String> inTwoFamilies(List<Class<?>> families) {
        Set<String> both = new LinkedHashSet<>();
        for (int i = 0; i < families.size(); i++) {
            for (Class<?> reason : reasonsIn(families.get(i))) {
                for (int j = i + 1; j < families.size(); j++) {
                    if (families.get(j).isAssignableFrom(reason)) {
                        both.add(reason.getSimpleName() + " is a "
                                + families.get(i).getSimpleName() + " and a "
                                + families.get(j).getSimpleName());
                    }
                }
            }
        }
        return both;
    }

    /**
     * The reasons a family stands for, which are its leaves and not its permitted names.
     *
     * <p>A permitted type may be sealed in turn, and what a measurement holds is a constant of the
     * type at the end of that. Asked with {@link Class#isAssignableFrom} rather than by comparing
     * the permitted lists: a reason reaches a second family through whatever intermediate it likes,
     * and a list held against a list would see only the ones written side by side.
     */
    private static List<Class<?>> reasonsIn(Class<?> family) {
        Class<?>[] permitted = family.getPermittedSubclasses();
        if (permitted == null) {
            return List.of(family);
        }
        List<Class<?>> out = new ArrayList<>();
        for (Class<?> each : permitted) {
            out.addAll(reasonsIn(each));
        }
        return out;
    }
}
