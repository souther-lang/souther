package souther.test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

/**
 * What one module compiled, read off its class files.
 *
 * <p>The mechanism a check on names needs, and none of the policy. Which names a module reserves
 * and what they may answer is that module's to say; finding the classes and reading a declaration's
 * type off them is the same work wherever it is asked, and written out per module it drifts — the
 * copy that stops seeing record components goes on reporting a pass.
 *
 * <p><b>One module, found from a class of it.</b> Not a walk over whatever {@code target/classes}
 * directories exist beside it: a module built earlier in the reactor may have last run's classes
 * on disk and a module not built at all has none, so a check that swept the file system would prove
 * something about a build nobody ran. A marker class is loaded from the classpath the test was
 * given, which is the module as this run built it.
 */
public final class WhatAModuleDeclares {

    private final List<ClassModel> classes;

    private WhatAModuleDeclares(List<ClassModel> classes) {
        this.classes = List.copyOf(classes);
    }

    /**
     * The classes of the module {@code marker} was compiled into.
     *
     * @param marker any class of that module's main sources
     */
    public static WhatAModuleDeclares of(Class<?> marker) {
        String binary = marker.getName();
        String simple = binary.substring(binary.lastIndexOf('.') + 1);
        Path root;
        try {
            root = Path.of(marker.getResource(simple + ".class").toURI());
        } catch (URISyntaxException e) {
            throw new IllegalStateException("a class of " + binary + " is not on a file system,"
                    + " so this module's classes cannot be read", e);
        }
        for (int up = 0; up <= binary.chars().filter(each -> each == '.').count(); up++) {
            root = root.getParent();
        }
        List<ClassModel> found = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path each : walk.filter(one -> one.toString().endsWith(".class")).sorted()
                    .toList()) {
                found.add(ClassFile.of().parse(Files.readAllBytes(each)));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return new WhatAModuleDeclares(found);
    }

    /** Every class of it. */
    public List<ClassModel> classes() {
        return classes;
    }

    /**
     * Every declaration of it that goes by one of {@code names}.
     *
     * <p>One name of one class is one of these. A record component, the field it writes and the
     * accessor that answers it are one thing the author wrote, and so are a field and the accessor
     * beside it; naming each would say the same thing three times over.
     *
     * <p>So a record whose component takes one of the names covers a second declaration of that
     * name in the same record — a static field, which is the only way to write one. Telling a
     * component's own field and accessor from a member that merely shares its name is not something
     * a class file says.
     */
    public List<Declared> taking(Set<String> names) {
        List<Declared> found = new ArrayList<>();
        for (ClassModel each : classes) {
            found.addAll(takenIn(each, names));
        }
        return found;
    }

    private static List<Declared> takenIn(ClassModel of, Set<String> names) {
        List<Declared> found = new ArrayList<>();
        Set<String> said = new LinkedHashSet<>();
        Set<String> components = new LinkedHashSet<>();
        for (RecordComponentInfo each : of.findAttribute(Attributes.record())
                .map(RecordAttribute::components).orElse(List.of())) {
            String name = each.name().stringValue();
            components.add(name);
            if (names.contains(name) && said.add(name)) {
                found.add(new Declared(of, name, signatureOf(each)));
            }
        }
        for (FieldModel each : of.fields()) {
            String name = each.fieldName().stringValue();
            if (names.contains(name) && !components.contains(name) && said.add(name)) {
                found.add(new Declared(of, name, signatureOf(each)));
            }
        }
        for (MethodModel each : of.methods()) {
            String name = each.methodName().stringValue();
            if (names.contains(name) && !components.contains(name) && said.add(name)) {
                found.add(new Declared(of, name, answeredBy(each)));
            }
        }
        return found;
    }

    /** One declaration, and what it answers. */
    public record Declared(ClassModel owner, String name, Signature type) {

        /** What the class holding it is called, as a class file spells it. */
        public String ownerName() {
            return owner.thisClass().asInternalName();
        }

        /** What the declaration reads as, for a check saying which one it found. */
        public String shown() {
            return ownerName() + "." + name + " : " + Signatures.shown(type);
        }
    }

    private static Signature answeredBy(MethodModel of) {
        return of.findAttribute(Attributes.signature())
                .map(it -> MethodSignature.parseFrom(it.signature().stringValue()).result())
                .orElseGet(() -> Signature.of(of.methodTypeSymbol().returnType()));
    }

    private static Signature signatureOf(FieldModel of) {
        return of.findAttribute(Attributes.signature())
                .map(it -> Signature.parseFrom(it.signature().stringValue()))
                .orElseGet(() -> Signature.of(of.fieldTypeSymbol()));
    }

    private static Signature signatureOf(RecordComponentInfo of) {
        return of.findAttribute(Attributes.signature())
                .map(it -> Signature.parseFrom(it.signature().stringValue()))
                .orElseGet(() -> Signature.of(of.descriptorSymbol()));
    }
}
