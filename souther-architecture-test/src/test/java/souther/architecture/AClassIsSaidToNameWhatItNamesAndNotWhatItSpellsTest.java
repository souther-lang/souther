package souther.architecture;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class is said to name another where it is a type of its members or a type it uses, and not
 * where its text happens to spell a descriptor.
 *
 * <p>{@link CompiledOutputs#classesNamedBy} is what the rules about which classes depend on which
 * ask. It names a class from a class entry, from the descriptor of a member or of what a member
 * refers to, and from a signature. A string a class holds is none of these, so a rule about
 * dependencies is not answered by what a class says in a message.
 */
class AClassIsSaidToNameWhatItNamesAndNotWhatItSpellsTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofEverythingCompiledHere();

    /** Spells a descriptor and depends on nothing it spells. */
    static final class Spelling {
        static final String DESCRIPTION = "Lsouther/compiler/values/Value;";

        String say() {
            return "Lsouther/compiler/values/Value<";
        }
    }

    /** Names its classes only in what it is declared with. */
    static final class Declared {
        BigDecimal field;

        Map<String, List<BigInteger>> generic;

        @SuppressWarnings("unused")
        static void parameter(Declared one) { }

        @SuppressWarnings("unused")
        static Runnable returned() {
            return null;
        }
    }

    @Test
    void whatAClassSpellsIsNotWhatItNames() {
        assertFalse(namedBy(Spelling.class).stream().anyMatch(
                        name -> name.startsWith("souther/compiler/values/")),
                () -> "a string is not a dependency: " + namedBy(Spelling.class));
    }

    @Test
    void whatAClassIsDeclaredWithIsNamed() {
        assertTrue(namedBy(Declared.class).containsAll(List.of(
                        "java/math/BigDecimal", "java/math/BigInteger", "java/util/Map",
                        "java/util/List", "java/lang/Runnable",
                        "souther/architecture/AClassIsSaidToNameWhatItNamesAndNotWhatItSpellsTest$Declared")),
                () -> "a field, a type argument, a parameter and a return type: "
                        + namedBy(Declared.class));
        assertEquals(true, namedBy(Declared.class).contains("java/math/BigInteger"));
    }

    private static java.util.Set<String> namedBy(Class<?> subject) {
        return CompiledOutputs.classesNamedBy(
                COMPILED.read(subject.getName().replace('.', '/')));
    }
}
