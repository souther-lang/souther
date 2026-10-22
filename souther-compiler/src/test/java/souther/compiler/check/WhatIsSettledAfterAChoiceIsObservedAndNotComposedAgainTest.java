package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.Method;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a choice leaves a position is composed once, and what leaves that reading is an observation.
 *
 * <p>The alternatives of a choice are readings of the whole value, so what one leaves a position is
 * settled where both of the languages that decide a branch's fate are held ({@link Confinement}).
 * A second composition of the same choice is a second answer about one model, and the two agree
 * only until somebody changes one of them — which is what this stops, on the one thing that leaves
 * that reading.
 *
 * <p><b>Said of the operations and not of their names.</b> Forbidding {@code join} and {@code
 * either} leaves the next algebra to be written under another name; what an algebra is, is an
 * operation over its own type, and there is none here. What may be asked of
 * {@link SettledOrderEnvelope} is where a position stops, and the answer to that is not another one
 * of these.
 */
class WhatIsSettledAfterAChoiceIsObservedAndNotComposedAgainTest {

    /**
     * Nothing anywhere takes one of these and answers with another.
     *
     * <p>Over every class this compiler holds and not over the type alone: an algebra written
     * beside it — a static method over two of them, a builder holding one and returning one — is
     * the same second answer arrived at from outside.
     *
     * <p>The classes the compiler compiles and no others: the modules below it cannot name this
     * type, and a test's fixture holding one is no reader this is about.
     */
    @Test
    void nothingTakesASettledOrderAndAnswersWithAnother() {
        Set<String> composing = new TreeSet<>();
        int mentioning = 0;
        for (ClassModel each : WhatWasCompiled.compiled().all()) {
            String named = each.thisClass().asInternalName().replace('/', '.');
            for (MethodModel method : each.methods()) {
                MethodTypeDesc type = method.methodTypeSymbol();
                boolean takes = type.parameterList().contains(ENVELOPE);
                if (method.methodName().equalsString("<init>")) {
                    // A constructor answers with the class it is of, so one taking a settled order
                    // is a reader holding what it was handed. The exception is this type's own:
                    // made from another of these, it would be the same operation under the one
                    // name that does not read as one.
                    if (takes) {
                        mentioning++;
                        if (each.thisClass().asSymbol().equals(ENVELOPE)) {
                            composing.add(named + ".<init>");
                        }
                    }
                    continue;
                }
                boolean answers = type.returnType().equals(ENVELOPE);
                if (!takes && !answers) {
                    continue;
                }
                mentioning++;
                if (takes && answers) {
                    composing.add(named + "." + method.methodName().stringValue());
                }
            }
        }
        assertTrue(mentioning > 0,
                "found nothing that is asked about a settled order at all — the scan missed it");
        assertEquals(Set.of(), composing,
                "an operation over two of these is a second composition of one choice, and the"
                        + " model it answers about is the same one the first composed");
    }

    /**
     * And the one that makes them is asked for an order, which only the reading that composes one
     * holds.
     *
     * <p>The other half of the same rule. What is here came from a reading that had spent the
     * connectives, and the way that is kept true is that a caller cannot arrive with an envelope of
     * its own: the way in wants what {@code WhatDecidesWhetherAValueExistsHoldsBothLanguagesTest}
     * lets only {@link Confinement} hold.
     */
    @Test
    void andTheOneWayInWantsAnOrderNobodyButTheReadingHolds() {
        Set<String> made = new TreeSet<>();
        for (Method each : SettledOrderEnvelope.class.getDeclaredMethods()) {
            if (each.getReturnType() != SettledOrderEnvelope.class) {
                continue;
            }
            made.add(each.getName() + "/" + (each.getParameterCount() == 0 ? "nothing"
                    : each.getParameterTypes()[0].getSimpleName()));
        }
        // Both of them, written out: a way in that says nothing is one nothing can be read off, and
        // a way in that is given a reading's answer is one only that reading can take. A third
        // fails here whichever of the two it looks like.
        assertEquals(Set.of("of/OrderedIntervals", "nothing/nothing"), made,
                "an envelope is made from an order and from nothing else, and an order is held by"
                        + " the reading that composed the connectives over it");
    }

    /**
     * A settled order, as a class file names it.
     *
     * <p>Read off what this module compiled to rather than off classes loaded for it: what is asked
     * is what a type declares, and the class file says that without the type being loaded.
     */
    private static final ClassDesc ENVELOPE = SettledOrderEnvelope.class.describeConstable()
            .orElseThrow();
}
