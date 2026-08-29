package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.codegen.Backend;
import souther.compiler.jvm.ClassFileImage;

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
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    /**
     * Enough of a module to write all three of the annotations this compiler puts on a class, and to
     * put something in every member of each.
     *
     * <p>Every array member holds at least one element on purpose. An empty array says its own name
     * and nothing about what it holds, so a member left empty here would be one whose element type
     * could change without the record moving. What keeps that from going unnoticed is
     * {@link #everyMemberOfTheRecordWasMeasured}, which refuses a record that could not read one.
     */
    private static final String MODULE = """
            module shared.money exposing ( Amount, Receipt, charge, quote )
            import String ( length )

            data Amount = Int
                invariant value >= 0 && withinCap(value)

            data Receipt = { paid: Amount }

            let withinCap (n: Int) = n <= 1000

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
    private static String carried(Map<String, ClassFileImage> classes) {
        Map<String, String> byAnnotation = new TreeMap<>();
        for (ClassFileImage image : classes.values()) {
            for (Annotation annotation : annotations(image.bytes())) {
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

    /** An array the fixture left empty, which says its own name and nothing about what it holds. */
    private static final String UNREAD = "nothing";

    /**
     * What a member holds, as coarsely as the wire distinguishes it: a value of another kind is a
     * member a reader of this number cannot take.
     *
     * <p>Every kind a class file can carry, and no default. A word this did not have was written as
     * whatever Java calls the class it arrived as, which records a shape in a vocabulary nothing
     * decided — and a boundary described in words nobody chose is one a reader of the record cannot
     * hold a compiler to. Listed out, a kind this does not have a word for is a compile error here
     * rather than a line in the record.
     */
    private static String kindOf(AnnotationValue value) {
        return switch (value) {
            case AnnotationValue.OfString _ -> "string";
            case AnnotationValue.OfBoolean _ -> "boolean";
            case AnnotationValue.OfByte _ -> "byte";
            case AnnotationValue.OfChar _ -> "char";
            case AnnotationValue.OfShort _ -> "short";
            case AnnotationValue.OfInt _ -> "int";
            case AnnotationValue.OfLong _ -> "long";
            case AnnotationValue.OfClass _ -> "class";
            case AnnotationValue.OfFloat _ -> "float";
            case AnnotationValue.OfDouble _ -> "double";
            case AnnotationValue.OfEnum e -> "enum " + e.className().stringValue();
            case AnnotationValue.OfAnnotation a -> "annotation "
                    + a.annotation().className().stringValue();
            // Said as what it is rather than guessed at. An empty array read as an array of strings
            // records a shape nothing measured, and the member's element type could then move
            // without this moving with it.
            case AnnotationValue.OfArray array -> "array of "
                    + (array.values().isEmpty() ? UNREAD : kindOf(array.values().getFirst()));
        };
    }

    private static List<Annotation> annotations(byte[] bytes) {
        return ClassFile.of().parse(bytes)
                .findAttribute(Attributes.runtimeInvisibleAnnotations())
                .map(a -> List.copyOf(a.annotations()))
                .orElse(List.of());
    }

    /**
     * The record says what every member holds, or the fixture is not wide enough to be a record.
     *
     * <p>Beside the comparison rather than folded into it. A member the fixture leaves empty
     * compares equal to itself forever, so the boundary would be recorded with a hole in it and the
     * record would go on passing — which is the shape of the defect this whole test is about, one
     * member in.
     */
    @Test
    void everyMemberOfTheRecordWasMeasured() {
        String carried = carried(Compiler.compile(MODULE));

        assertFalse(carried.contains(UNREAD),
                () -> "a member of the boundary is written by a fixture that leaves it empty, so"
                        + " what it holds is not recorded and could move without this noticing."
                        + " Give it a value in MODULE:\n\n" + carried);
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
