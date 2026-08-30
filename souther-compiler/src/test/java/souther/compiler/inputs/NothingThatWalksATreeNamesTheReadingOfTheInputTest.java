package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.classfile.Attributes;
import java.lang.classfile.AttributedElement;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.attribute.RuntimeInvisibleAnnotationsAttribute;
import java.lang.classfile.attribute.RuntimeInvisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.RuntimeVisibleAnnotationsAttribute;
import java.lang.classfile.attribute.RuntimeVisibleTypeAnnotationsAttribute;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.MethodTypeEntry;
import java.lang.classfile.constantpool.NameAndTypeEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing that walks a tree names the reading of the input.
 *
 * <p>The two are told apart by how long each of them lives. {@link InputReads} is a function of the
 * program point — the bindings gone under, the arm gone into — and changes at every step of a walk;
 * {@link InputDomain} is one value for a whole analysis. Held together, the reading is copied into
 * every step and each reader asks whichever copy it is holding, which is how a reader comes to take
 * an answer off a value that is only carrying it.
 *
 * <p><b>Which values those are is worked out and not listed.</b> A value that walks a tree is
 * {@link InputReads} and anything that keeps one — {@link Denotation} keeps one so a value can say
 * what it was read in, and so do the records a reader files a comparison under. Written as a list,
 * this checked the two types that had just been edited and passed while a third kept both, which is
 * the defect it exists to find. So the subject is every class of this compiler whose fields hold an
 * environment, and the list below only says the walk found the ones already known.
 *
 * <p><b>What counts as naming a type is a role and not an entry.</b> A class file spells a type in a
 * class reference, a field or method descriptor, a generic signature, a method type, the type of a
 * member it links against, an annotation's own type, and a class an annotation was given as an
 * element. Each of those is read here as what it is. Nothing is subtracted afterwards: text a class
 * carries as a string constant is never one of these roles, so it never arrives — and a descriptor
 * that happens to read the same as some string constant is still a descriptor, which subtracting by
 * the entry they share would have thrown away.
 *
 * <p>So this is a claim about what Java links against, and not about what is reachable: a class
 * named as text and found by reflection would not be seen here.
 */
class NothingThatWalksATreeNamesTheReadingOfTheInputTest {

    private static final String ENVIRONMENT = "souther/compiler/inputs/InputReads";
    private static final String READING = "souther/compiler/inputs/InputDomain";

    /** The environment itself, which holds no environment of its own to be found by. */
    private static final String ROOT = ENVIRONMENT;

    @Test
    void noValueThatWalksATreeNamesTheReading() throws IOException, URISyntaxException {
        Map<String, Set<String>> named = new LinkedHashMap<>();
        for (ClassModel each : compiled()) {
            String name = each.thisClass().asInternalName();
            if (!name.equals(ROOT) && !holdsAnEnvironment(each)) {
                continue;
            }
            Set<String> mentions = namesOfTypesIn(each).stream()
                    .filter(spelling -> spelling.contains(READING))
                    .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
            if (!mentions.isEmpty()) {
                named.put(name, mentions);
            }
        }
        assertEquals(Map.of(), named);
    }

    /**
     * And the subject is the values that walk a tree, which is what makes the emptiness above mean
     * anything.
     *
     * <p>Both halves. A walk that found none of them would report every class clean; one that found
     * only what was named here would be the list this exists not to be.
     */
    @Test
    void andTheSubjectIsEveryValueThatKeepsAnEnvironment() throws IOException, URISyntaxException {
        List<String> found = new ArrayList<>();
        for (ClassModel each : compiled()) {
            if (holdsAnEnvironment(each)) {
                found.add(each.thisClass().asInternalName());
            }
        }
        assertTrue(found.containsAll(List.of(
                        "souther/compiler/inputs/Denotation",
                        "souther/compiler/inputs/ComparedNumbers$Read",
                        "souther/compiler/partition/AffineReading$OfAComparison$Stopped",
                        "souther/compiler/partition/ComparisonReadings$Reading",
                        "souther/compiler/partition/Condition$Compares",
                        "souther/compiler/reading/CoverageNaming",
                        "souther/compiler/reading/NumberWays")),
                () -> "the walk reaches the values known to keep an environment, and found " + found);
    }

    /**
     * And each way a class file spells a type is one the walk reads.
     *
     * <p>The check above passes on the empty set, which is also what a walk that read nothing
     * produces. So each role is put through it on a class that names the reading that way.
     *
     * <p>The last of them is where subtracting by entry went wrong: a field of the reading's type
     * beside a string constant spelling that same descriptor, which javac holds as one
     * {@code Utf8}. Read by role the descriptor is still a descriptor.
     */
    @Test
    void andEachWayOfSpellingATypeIsRead() throws IOException {
        assertFinds(InAMethodDescriptor.class, "a method's descriptor");
        assertFinds(InAFieldDescriptor.class, "a field's descriptor");
        assertFinds(InAClassReference.class, "a class reference");
        assertFinds(InAMemberType.class, "the type of a member linked against");
        assertFinds(InAClassSignature.class, "a class's generic signature");
        assertFinds(InAMethodSignature.class, "a method's generic signature");
        assertFinds(InARecordComponent.class, "a record component");
        assertFinds(InAnAnnotation.class, "an annotation's element");
        assertFinds(InAMethodType.class, "a method type a bootstrap is handed");
        assertFinds(SharedWithAStringConstant.class,
                "a descriptor sharing its spelling with a string constant");
    }

    /** And a class that names the reading only as text is not read as naming it. */
    @Test
    void andTextIsNotASpelling() throws IOException {
        assertEquals(Set.of(), mentionsIn(OnlyAsAStringConstant.class));
    }

    /** And each witness is the shape it is named for, which is also what keeps its members read. */
    @Test
    void andEachWitnessIsTheShapeItIsNamedFor() {
        assertNull(InAMethodDescriptor.none());
        assertTrue(InAFieldDescriptor.isNull());
        assertFalse(InAClassReference.isOne("not one"));
        assertEquals(List.of(), InAMemberType.taken());
        assertTrue(new InAClassSignature().isEmpty());
        assertNull(InAMethodSignature.none());
        assertNull(new InARecordComponent(null).held());
        assertEquals(InputDomain.class, InAnAnnotation.class.getAnnotation(Names.class).value());
        assertNull(InAMethodType.none().get());
        assertTrue(SharedWithAStringConstant.isNull());
        assertEquals("Lsouther/compiler/inputs/InputDomain;", SharedWithAStringConstant.SPELLED);
        assertEquals("Lsouther/compiler/inputs/InputDomain;", OnlyAsAStringConstant.SPELLED);
    }

    private static void assertFinds(Class<?> of, String how) throws IOException {
        assertFalse(mentionsIn(of).isEmpty(), () -> "the reading named in " + how + " is read");
    }

    private static Set<String> mentionsIn(Class<?> of) throws IOException {
        Set<String> out = new LinkedHashSet<>();
        for (String spelling : namesOfTypesIn(parsed(of))) {
            if (spelling.contains(READING)) {
                out.add(spelling);
            }
        }
        return out;
    }

    /** Whether {@code of} keeps an environment, which is what makes it walk a tree. */
    private static boolean holdsAnEnvironment(ClassModel of) {
        for (FieldModel field : of.fields()) {
            if (field.fieldType().stringValue().equals("L" + ENVIRONMENT + ";")
                    || signatureOf(field).contains(ENVIRONMENT)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Every spelling of a type in {@code of}, each read as the role it is written in.
     *
     * <p>The roles, and there is nothing else a class file names a type with. A class reference
     * carries supertypes, what is caught, what is tested against and what is built. A descriptor
     * carries what a field holds and what a method takes and answers, and the type half of a member
     * this links against carries the same for the other side. A generic signature carries what an
     * erasure left out, on a class, a method, a field or a record component. A method type carries
     * what a bootstrap is handed. And an annotation carries its own type and any class it was given
     * as an element.
     */
    private static Set<String> namesOfTypesIn(ClassModel of) {
        Set<String> out = new LinkedHashSet<>();
        for (PoolEntry entry : of.constantPool()) {
            switch (entry) {
                case ClassEntry named -> out.add(named.asInternalName());
                case NameAndTypeEntry member -> out.add(member.type().stringValue());
                case MethodTypeEntry taken -> out.add(taken.descriptor().stringValue());
                default -> { }
            }
        }
        out.add(signatureOf(of));
        annotationsOf(of, out);
        for (FieldModel field : of.fields()) {
            out.add(field.fieldType().stringValue());
            out.add(signatureOf(field));
            annotationsOf(field, out);
        }
        for (MethodModel method : of.methods()) {
            out.add(method.methodType().stringValue());
            out.add(signatureOf(method));
            annotationsOf(method, out);
        }
        for (RecordComponentInfo component : of.findAttribute(Attributes.record())
                .map(RecordAttribute::components).orElse(List.of())) {
            out.add(component.descriptor().stringValue());
            out.add(component.findAttribute(Attributes.signature())
                    .map(SignatureAttribute::signature).map(each -> each.stringValue()).orElse(""));
            annotationsOf(component, out);
        }
        return out;
    }

    private static String signatureOf(AttributedElement of) {
        return of.findAttribute(Attributes.signature())
                .map(each -> each.signature().stringValue()).orElse("");
    }

    private static void annotationsOf(AttributedElement of, Set<String> out) {
        List<java.lang.classfile.Annotation> written = new ArrayList<>();
        of.findAttribute(Attributes.runtimeVisibleAnnotations())
                .map(RuntimeVisibleAnnotationsAttribute::annotations).ifPresent(written::addAll);
        of.findAttribute(Attributes.runtimeInvisibleAnnotations())
                .map(RuntimeInvisibleAnnotationsAttribute::annotations).ifPresent(written::addAll);
        of.findAttribute(Attributes.runtimeVisibleTypeAnnotations())
                .map(RuntimeVisibleTypeAnnotationsAttribute::annotations)
                .ifPresent(each -> each.forEach(one -> written.add(one.annotation())));
        of.findAttribute(Attributes.runtimeInvisibleTypeAnnotations())
                .map(RuntimeInvisibleTypeAnnotationsAttribute::annotations)
                .ifPresent(each -> each.forEach(one -> written.add(one.annotation())));
        written.forEach(one -> take(one, out));
    }

    private static void take(java.lang.classfile.Annotation written, Set<String> out) {
        out.add(written.className().stringValue());
        written.elements().forEach(element -> take(element.value(), out));
    }

    private static void take(java.lang.classfile.AnnotationValue value, Set<String> out) {
        switch (value) {
            case java.lang.classfile.AnnotationValue.OfClass named ->
                    out.add(named.className().stringValue());
            case java.lang.classfile.AnnotationValue.OfEnum named ->
                    out.add(named.className().stringValue());
            case java.lang.classfile.AnnotationValue.OfAnnotation nested ->
                    take(nested.annotation(), out);
            case java.lang.classfile.AnnotationValue.OfArray several ->
                    several.values().forEach(each -> take(each, out));
            default -> { }
        }
    }

    /** Every class this compiler was built into, found from where one of them is loaded from. */
    private static List<ClassModel> compiled() throws IOException, URISyntaxException {
        Path from = Path.of(InputReads.class.getResource("InputReads.class").toURI());
        Path root = from;
        for (int up = 0; up <= ENVIRONMENT.chars().filter(each -> each == '/').count(); up++) {
            root = root.getParent();
        }
        List<ClassModel> out = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path each : walk.filter(one -> one.toString().endsWith(".class")).sorted()
                    .toList()) {
                out.add(ClassFile.of().parse(Files.readAllBytes(each)));
            }
        }
        return out;
    }

    private static ClassModel parsed(Class<?> of) throws IOException {
        String binary = of.getName();
        String resource = binary.substring(binary.lastIndexOf('.') + 1) + ".class";
        try (var in = of.getResourceAsStream(resource)) {
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

        static boolean isNull() {
            return none == null;
        }
    }

    private static final class InAClassReference {
        static boolean isOne(Object what) {
            return what instanceof InputDomain;
        }
    }

    private static final class InAMemberType {
        static Object taken() {
            return InputDomain.NONE.positions();
        }
    }

    private static final class InAClassSignature extends java.util.ArrayList<InputDomain> {
        private static final long serialVersionUID = 1L;
    }

    private static final class InAMethodSignature {
        static java.util.ArrayList<InputDomain> none() {
            return null;
        }
    }

    private record InARecordComponent(InputDomain held) {
    }

    @Names(InputDomain.class)
    private static final class InAnAnnotation {
    }

    private static final class InAMethodType {
        static Supplier<InputDomain> none() {
            return () -> null;
        }
    }

    /**
     * A field of the reading's type beside a string constant spelling that same descriptor. One
     * {@code Utf8} holds both, so a walk that took string constants out by the entry they use took
     * the field's descriptor with them.
     */
    private static final class SharedWithAStringConstant {
        static final String SPELLED = "Lsouther/compiler/inputs/InputDomain;";

        private static InputDomain none;

        static boolean isNull() {
            return none == null;
        }
    }

    /** And the same string constant with nothing of the reading's type beside it. */
    private static final class OnlyAsAStringConstant {
        static final String SPELLED = "Lsouther/compiler/inputs/InputDomain;";
    }
}
