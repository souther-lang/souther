package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.constantpool.StringEntry;
import java.lang.classfile.constantpool.Utf8Entry;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name in a tree stands for is answered by a value that cannot reach the reading of the
 * input.
 *
 * <p>The two are told apart by how long each of them lives. {@link InputReads} is a function of the
 * program point — the bindings gone under, the arm gone into — and changes at every step of a walk;
 * {@link InputDomain} is one value for a whole analysis. Held together, the reading was copied into
 * every step and each reader asked whichever copy it was holding, which is how a reader came to
 * take an answer off a value that was only carrying it.
 *
 * <p>{@link Denotation} is here for the same reason: it is the environment travelling with a value
 * the environment explains, so a reading put on it is a reading back inside the walk one step
 * further out.
 *
 * <p><b>Every way a class file names a type is one spelling.</b> A class name, a field or method
 * descriptor, a generic signature, an annotation's type or element, a method type, the arguments a
 * bootstrap is given — each of them is held as a {@code Utf8} of the constant pool, whatever
 * attribute points at it. So this reads the pool rather than a list of the attributes there happen
 * to be today, which is what a list would have to be kept in step with as the class file format
 * grows.
 *
 * <p><b>The one thing left out is a string constant</b>, taken out by which pool entry it is and
 * not by what it says, so a descriptor that happens to equal one is still read. This is therefore a
 * claim about what Java links against and not about what is reachable: a class named as text and
 * found by reflection would not be seen here.
 *
 * <p>It over-approximates in the other direction — a member or attribute name that spelled the
 * reading would be reported too — which for something being forbidden is the side to be wrong on.
 */
class WhatATreesNamesAreReadInDoesNotReachTheReadingOfTheInputTest {

    private static final String READING = "souther/compiler/inputs/InputDomain";

    @Test
    void theNameEnvironmentNamesTheReadingNowhere() throws IOException {
        assertEquals(Set.of(), mentionsOfTheReadingIn(InputReads.class));
    }

    @Test
    void andNeitherDoesTheValueAnEnvironmentTravelsWith() throws IOException {
        assertEquals(Set.of(), mentionsOfTheReadingIn(Denotation.class));
    }

    /**
     * What is above passes on the empty set, which is also what a class file nothing could read
     * produces. So each way of naming a type that the prohibition covers is put through the same
     * walk on a class that names the reading that way.
     *
     * <p>What each witness settles is that the way it names the reading does put a spelling in the
     * pool — which is what the walk rests on. Six of them name it that way and no other; the
     * bootstrap one cannot, because the method type a lambda's bootstrap is given is the same
     * spelling as the method it points at.
     */
    @Test
    void andEachWayOfNamingATypeIsFound() throws IOException {
        assertFinds(InAMethodDescriptor.class, "a method's descriptor");
        assertFinds(InAFieldDescriptor.class, "a field's descriptor");
        assertFinds(InAnInstruction.class, "an instruction's operand");
        assertFinds(InAClassSignature.class, "a class's generic signature");
        assertFinds(InAMethodSignature.class, "a method's generic signature");
        assertFinds(InAnAnnotation.class, "an annotation's element");
        assertFinds(InABootstrapArgument.class, "a bootstrap method's argument");
    }

    /** And each witness is the shape it is named for, which is also what keeps its members read. */
    @Test
    void andEachWitnessIsTheShapeItIsNamedFor() {
        assertNull(InAMethodDescriptor.none());
        assertTrue(InAFieldDescriptor.isNull());
        assertFalse(InAnInstruction.isOne("not one"));
        assertTrue(new InAClassSignature().isEmpty());
        assertNull(InAMethodSignature.none());
        assertEquals(InputDomain.class, InAnAnnotation.class.getAnnotation(Names.class).value());
        assertNull(InABootstrapArgument.none().get());
    }

    private static void assertFinds(Class<?> of, String how) throws IOException {
        assertFalse(mentionsOfTheReadingIn(of).isEmpty(),
                () -> "the reading named in " + how + " is found");
    }

    /** Every spelling in {@code of}'s class file that names the reading. */
    private static Set<String> mentionsOfTheReadingIn(Class<?> of) throws IOException {
        ClassModel model = parsed(of);
        // By which entry it is and not by what it says: a descriptor that reads the same as some
        // string constant is still a descriptor.
        Set<Integer> constants = new HashSet<>();
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof StringEntry text) {
                constants.add(text.utf8().index());
            }
        }
        Set<String> found = new LinkedHashSet<>();
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof Utf8Entry spelling
                    && !constants.contains(spelling.index())
                    && spelling.stringValue().contains(READING)) {
                found.add(spelling.stringValue());
            }
        }
        return found;
    }

    /** The compiled class as the run time reads it, and not a path a build laid it out at. */
    private static ClassModel parsed(Class<?> of) throws IOException {
        String binary = of.getName();
        String resource = binary.substring(binary.lastIndexOf('.') + 1) + ".class";
        try (InputStream in = of.getResourceAsStream(resource)) {
            assertNotNull(in, () -> "the compiled " + binary + " is on the class path");
            return ClassFile.of().parse(in.readAllBytes());
        }
    }

    @Retention(RetentionPolicy.RUNTIME)
    private @interface Names {
        Class<?> value();
    }

    private static final class InAMethodDescriptor {
        static InputDomain none() {
            return null;
        }
    }

    private static final class InAFieldDescriptor {
        private static InputDomain none;

        /** Answered without naming the reading, so the field's own descriptor is the one spelling
         *  this witness has. */
        static boolean isNull() {
            return none == null;
        }
    }

    private static final class InAnInstruction {
        static boolean isOne(Object what) {
            return what instanceof InputDomain;
        }
    }

    private static final class InAClassSignature extends ArrayList<InputDomain> {
        private static final long serialVersionUID = 1L;
    }

    private static final class InAMethodSignature {
        static ArrayList<InputDomain> none() {
            return null;
        }
    }

    @Names(InputDomain.class)
    private static final class InAnAnnotation {
    }

    private static final class InABootstrapArgument {
        static Supplier<InputDomain> none() {
            return () -> null;
        }
    }
}
