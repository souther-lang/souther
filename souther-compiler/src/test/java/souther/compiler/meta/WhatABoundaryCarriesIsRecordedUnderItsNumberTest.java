package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.codegen.Backend;

import java.io.InputStream;
import java.lang.classfile.Annotation;
import java.lang.classfile.AnnotationElement;
import java.lang.classfile.AnnotationValue;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a compiled module carries across the boundary, held against the number that says which
 * boundary it is.
 *
 * <p>The shape is decided by {@link ModuleMetadata} and read by {@link SoutherAnnotations}; the
 * number is {@link Backend#BOUNDARY_VERSION}, written a few files away. Nothing compared the two, so
 * a member could be renamed or retyped and every test stay green — which is what happened when the
 * behavior annotation's {@code injected} flag became an {@code implementation} word (issue #936).
 * A jar and a compiler then agree on the number and disagree about the wire, which is the one thing
 * the number exists to prevent (ADR-0063).
 *
 * <p>Recorded per number rather than in one file that follows the shape. A record that moved with
 * the shape would be edited in the same commit that broke the boundary and say nothing; one named
 * for the number is missing until somebody raises it. The reverse is not held: the boundary covers
 * more than these members — what emitted code calls goes across it too — so the number may move
 * while this record stands.
 */
class WhatABoundaryCarriesIsRecordedUnderItsNumberTest {

    /** Enough of a module to write all three of the annotations this compiler puts on a class. */
    private static final String MODULE = """
            module shared.money exposing ( Amount, Receipt, charge, quote )
            import String ( length )

            data Amount = Int
                invariant value >= 0

            data Receipt = { paid: Amount }

            behavior charge : (a: Amount) -> Receipt
                constructs Receipt
            let charge (a) = Receipt { paid = a }

            behavior quote : (a: Amount) -> Receipt
            """;

    @Test
    void theShapeIsTheOneRecordedForThisBoundary() {
        String carried = carried(Compiler.compile(MODULE));
        String recorded = recorded(Backend.BOUNDARY_VERSION);

        assertNotNull(recorded, () ->
                "nothing records what boundary " + Backend.BOUNDARY_VERSION + " carries. A member"
                        + " renamed, retyped or dropped is a boundary a jar cannot be read across,"
                        + " so raise " + Backend.BOUNDARY_VERSION + " and write"
                        + " src/test/resources/" + resource(Backend.BOUNDARY_VERSION)
                        + " holding:\n\n" + carried);
        assertEquals(recorded, carried,
                "what a module carries is not what boundary " + Backend.BOUNDARY_VERSION
                        + " records. A jar written by another compiler at this number is read as"
                        + " this shape, so a shape that moved needs a number that moved with it.");
    }

    /** The members of each annotation this compiler writes, and what kind of value each holds. */
    private static String carried(Map<String, byte[]> classes) {
        Map<String, String> byAnnotation = new TreeMap<>();
        for (byte[] bytes : classes.values()) {
            for (Annotation annotation : annotations(bytes)) {
                String type = annotation.className().stringValue();
                if (!type.startsWith("Lsouther/runtime/meta/")) {
                    continue;
                }
                byAnnotation.put(type, members(annotation));
            }
        }
        StringBuilder out = new StringBuilder();
        byAnnotation.forEach((type, members) ->
                out.append(type).append('\n').append(members));
        return out.toString();
    }

    private static String members(Annotation annotation) {
        List<String> written = new ArrayList<>();
        for (AnnotationElement element : annotation.elements()) {
            written.add("  " + element.name().stringValue() + ": " + kindOf(element.value()));
        }
        java.util.Collections.sort(written);
        return String.join("\n", written) + "\n";
    }

    /** What a member holds, as coarsely as the wire distinguishes it: a value of another kind is a
     *  member a reader of this number cannot take. */
    private static String kindOf(AnnotationValue value) {
        return switch (value) {
            case AnnotationValue.OfString _ -> "string";
            case AnnotationValue.OfInt _ -> "int";
            case AnnotationValue.OfBoolean _ -> "boolean";
            case AnnotationValue.OfArray array -> "array of "
                    + (array.values().isEmpty() ? "string" : kindOf(array.values().get(0)));
            default -> value.getClass().getSimpleName();
        };
    }

    private static List<Annotation> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes)
                .findAttribute(Attributes.runtimeInvisibleAnnotations())
                .map(a -> List.copyOf(a.annotations()))
                .orElse(List.of());
    }

    private static String resource(int version) {
        return "souther/compiler/meta/boundary-" + version + ".txt";
    }

    private static String recorded(int version) {
        try (InputStream in = WhatABoundaryCarriesIsRecordedUnderItsNumberTest.class
                .getClassLoader().getResourceAsStream(resource(version))) {
            return in == null ? null : new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (java.io.IOException e) {
            throw new AssertionError(e);
        }
    }
}
