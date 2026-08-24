package souther.compiler.jvm;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A JVM class name can only be made by naming a Souther entity, and only here.
 *
 * <p>Measured against the shape of the API rather than against an answer, for the same reason the
 * resolution rule is: the rule that a reader asks rather than spells was written down on
 * {@code Backend.behaviorClass}, on {@code GeneratedBehavior}, and in the issue that led here, and was
 * restated at eleven sites all the same. A sentence is kept by whoever reads it; a signature is kept
 * by everyone.
 *
 * <p>What holds it is that {@link JvmClassName} has no constructor a caller can reach. The scan over
 * the built classes is a tripwire under this, not the other way round — it can be evaded and this
 * cannot.
 */
class NoPublicWayToMakeAGeneratedClassNameTest {

    @Test
    void aNameHasNoConstructorAReaderCanReach() {
        for (Constructor<?> c : JvmClassName.class.getDeclaredConstructors()) {
            assertFalse(Modifier.isPublic(c.getModifiers()) || Modifier.isProtected(c.getModifiers()),
                    "a reader outside this package could mint a name: " + c);
        }
        assertEquals(0, JvmClassName.class.getConstructors().length,
                "and none is reachable by reflection either");
    }

    /**
     * Every way in takes an identity. A public entry point that took a spelling would be the old API
     * back under a new name.
     *
     * <p>Two of them, because two kinds of thing have a class here and they are told apart by what
     * they are: one this compilation emits, and one the language declares whose class the runtime
     * ships (ADR-0087). Written out with the identity each takes rather than counted, so that a
     * third arriving is a decision somebody made here.
     */
    @Test
    void everyWayInTakesAnIdentity() {
        List<Method> makers = new ArrayList<>();
        for (Class<?> c : List.of(SoutherJvmAbi.class, GeneratedClasses.class, JvmClassName.class)) {
            for (Method m : c.getMethods()) {
                if (m.getDeclaringClass() != Object.class && m.getReturnType() == JvmClassName.class) {
                    makers.add(m);
                }
            }
        }

        assertEquals(List.of(SoutherJvmAbi.class, SoutherJvmAbi.class),
                makers.stream().map(Method::getDeclaringClass).toList(),
                () -> "a name is made in the ABI and nowhere else: " + makers);
        assertEquals(
                List.of("nameOf(GeneratedClass)", "nameOfLanguageDeclaration(TypeSymbol)"),
                makers.stream()
                        .map(m -> m.getName() + "("
                                + m.getParameterTypes()[0].getSimpleName() + ")")
                        .sorted().toList(),
                () -> "each takes what the thing is, and neither takes a spelling: " + makers);
    }

    /**
     * And a name it hands back cannot be taken apart into the pieces it was built from — those are
     * what a caller finishes by hand, and finishing by hand is the defect.
     *
     * <p>A whole answer to another question is not a piece of one: where a class of this name is
     * written is complete on its own, and a caller holding it has nothing left to finish.
     */
    @Test
    void andANameHandsBackNoPieceOfItself() {
        for (Method m : JvmClassName.class.getMethods()) {
            if (m.getDeclaringClass() != JvmClassName.class) {
                continue;
            }
            assertTrue(List.of("binaryName", "classDesc", "classFile", "is",
                            "equals", "hashCode", "toString").contains(m.getName()),
                    "a public member of a name that is not the whole name: " + m.getName());
        }
    }

    /** Every case of the sealed interface is answered — a new one that this ABI had no name for would
     *  not compile, and this says so where the guarantee is stated rather than leaving it to the next
     *  reader to notice the switch has no default. */
    @Test
    void everyGeneratedClassHasAName() {
        assertEquals(13, kindsOf(GeneratedClass.class).size(),
                "the kinds of class this compiler invents; changing this is changing the ABI");
    }

    /**
     * The kinds under {@code sealed}, with the interfaces between flattened out. An intermediate —
     * the classes a derived encoder may sit beside, say — narrows what can be built without being a
     * kind of class itself.
     */
    static List<Class<?>> kindsOf(Class<?> sealed) {
        List<Class<?>> kinds = new ArrayList<>();
        for (Class<?> c : sealed.getPermittedSubclasses()) {
            if (c.isRecord()) {
                kinds.add(c);
            } else {
                assertTrue(c.isSealed(), c + " is neither a record nor a narrowing of the kinds");
                kinds.addAll(kindsOf(c));
            }
        }
        return kinds;
    }
}
