package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.InputStream;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.NameAndTypeEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
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
 * <p><b>What this checks is a symbolic reference and not reachability.</b> A class file names the
 * types and members it links against — supertypes, field and method descriptors, generic
 * signatures, record components, annotations, and everything the code refers to — and none of those
 * may name the reading. A class name written as a string constant is not one of them, so a route
 * through reflection would not be found here. The check is as wide as Java's linking and no wider,
 * which is the whole of what it says.
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
     * The check reads a class file at all.
     *
     * <p>Both tests above pass on an empty set of mentions, which is what a class file that could
     * not be read produces. So one type that does name the reading is put through the same walk:
     * {@link InputNumber} is handed both — the environment for where a name stands and the reading
     * for what stands there — so its own methods name it.
     */
    @Test
    void andTheWalkFindsAMentionWhereThereIsOne() throws IOException {
        assertTrue(!mentionsOfTheReadingIn(InputNumber.class).isEmpty(),
                "a type that names the reading is found to name it");
    }

    /** Every place {@code of}'s class file names the reading, as the kind of reference each is. */
    private static Set<String> mentionsOfTheReadingIn(Class<?> of) throws IOException {
        ClassModel model = parsed(of);
        Set<String> found = new LinkedHashSet<>();
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof ClassEntry named && names(named.asInternalName())) {
                found.add("class reference " + named.asInternalName());
            }
            if (entry instanceof NameAndTypeEntry member && names(member.type().stringValue())) {
                found.add("member of type " + member.type().stringValue());
            }
        }
        for (FieldModel field : model.fields()) {
            take("field " + field.fieldName().stringValue(),
                    field.fieldType().stringValue(), found);
            field.findAttribute(Attributes.signature()).ifPresent(each ->
                    take("field signature " + field.fieldName().stringValue(),
                            each.signature().stringValue(), found));
        }
        for (MethodModel method : model.methods()) {
            take("method " + method.methodName().stringValue(),
                    method.methodType().stringValue(), found);
            method.findAttribute(Attributes.signature()).ifPresent(each ->
                    take("method signature " + method.methodName().stringValue(),
                            each.signature().stringValue(), found));
        }
        for (RecordComponentInfo component : model.findAttribute(Attributes.record())
                .map(RecordAttribute::components).orElse(java.util.List.of())) {
            take("record component " + component.name().stringValue(),
                    component.descriptor().stringValue(), found);
            component.findAttribute(Attributes.signature())
                    .map(SignatureAttribute::signature)
                    .ifPresent(each -> take("record component signature "
                            + component.name().stringValue(), each.stringValue(), found));
        }
        return found;
    }

    private static void take(String where, String descriptor, Set<String> found) {
        if (names(descriptor)) {
            found.add(where + " : " + descriptor);
        }
    }

    private static boolean names(String descriptor) {
        return descriptor.contains(READING);
    }

    /** The compiled class as the run time reads it, and not a path a build laid it out at. */
    private static ClassModel parsed(Class<?> of) throws IOException {
        String resource = of.getSimpleName() + ".class";
        try (InputStream in = of.getResourceAsStream(resource)) {
            assertNotNull(in, () -> "the compiled " + of.getName() + " is on the class path");
            return ClassFile.of().parse(in.readAllBytes());
        }
    }
}
