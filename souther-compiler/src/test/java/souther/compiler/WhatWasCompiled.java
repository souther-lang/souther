package souther.compiler;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.ConstantPool;
import java.lang.classfile.constantpool.MethodTypeEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.constant.ClassDesc;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

/**
 * What this module compiled to, for a rule about who may depend on what.
 *
 * <p>A structural rule read off the source reads the spellings that are there today. "A file saying
 * {@code implements X}" is not the set of things that answer {@code X} — a lambda answers one and
 * says neither word, and the next one to get this wrong will be written the way the last one was
 * not. So the set is taken from what javac made of the module, where an anonymous body, a class and
 * a lambda are all present and all say what they are.
 *
 * <p>Read from {@code target/classes}, which is what surefire was handed and what the tests using
 * this were compiled against. A walk finding nothing is a walk of the wrong directory, so
 * {@link #classes} says so rather than reporting an empty set as a clean one.
 */
public final class WhatWasCompiled {

    private static final Path CLASSES = Path.of("target/classes");

    /** Every class this module compiled, by binary name. */
    public static List<String> classes() {
        List<String> found = new ArrayList<>();
        try (Stream<Path> written = Files.walk(CLASSES)) {
            for (Path each : written.filter(p -> p.toString().endsWith(".class")).sorted().toList()) {
                found.add(CLASSES.relativize(each).toString()
                        .replace(java.io.File.separatorChar, '.')
                        .replaceAll("\\.class$", ""));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        if (found.isEmpty()) {
            throw new IllegalStateException(CLASSES.toAbsolutePath()
                    + " holds no classes, so a rule read from it holds nothing");
        }
        return found;
    }

    /**
     * Every class that answers {@code answered} — by implementing it, or by being the class a lambda
     * of it was made in.
     *
     * <p>A lambda is not a class of its own: it is an {@code invokedynamic} in the class that writes
     * it, whose type is the interface it answers. So what this names for one is where it was
     * written, which is the file a rule about what an answer may depend on is about anyway.
     */
    public static Set<String> answering(Class<?> answered) {
        ClassDesc asked = answered.describeConstable().orElseThrow();
        Set<String> found = new LinkedHashSet<>();
        for (String each : classes()) {
            ClassModel model = parse(each);
            if (reaches(model, asked, new LinkedHashSet<>()) || lambdaOf(model, asked)) {
                found.add(each);
            }
        }
        return found;
    }

    /**
     * Whether {@code model} is an {@code asked}, through however many types in between.
     *
     * <p>Directly or not. An interface between the two is a way of answering it and not a way of
     * not answering it, and a rule reading only the interfaces named on the class itself would let
     * one through for the length of one declaration.
     */
    private static boolean reaches(ClassModel model, ClassDesc asked, Set<ClassDesc> seen) {
        List<ClassDesc> above = new ArrayList<>();
        model.superclass().ifPresent(each -> above.add(each.asSymbol()));
        model.interfaces().forEach(each -> above.add(each.asSymbol()));
        for (ClassDesc each : above) {
            if (each.equals(asked)) {
                return true;
            }
            if (!seen.add(each)) {
                continue;
            }
            ClassModel further = parsedOrNull(each.packageName().isEmpty()
                    ? each.displayName()
                    : each.packageName() + "." + each.displayName());
            if (further != null && reaches(further, asked, seen)) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code model} makes a lambda whose type is {@code asked}: the interface a functional
     *  method is bound to is the return of the {@code invokedynamic}'s type. */
    private static boolean lambdaOf(ClassModel model, ClassDesc asked) {
        ConstantPool pool = model.constantPool();
        for (int i = 1; i < pool.size(); i++) {
            PoolEntry entry;
            try {
                entry = pool.entryByIndex(i);
            } catch (Exception _) {
                continue;   // a wide entry's second slot, which has no entry of its own
            }
            if (entry instanceof java.lang.classfile.constantpool.InvokeDynamicEntry asDynamic
                    && asDynamic.typeSymbol().returnType().equals(asked)) {
                return true;
            }
            if (entry instanceof MethodTypeEntry asType
                    && asType.asSymbol().returnType().equals(asked)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Every class that calls {@code method} on {@code on}.
     *
     * <p>For a rule about who may do something rather than about who may name a type. A call is in
     * the caller's constant pool whatever it is spelled like at the call site, and a lambda's body
     * is compiled into the class that wrote it, so a caller cannot get out of this by writing the
     * call somewhere shorter.
     */
    public static Set<String> callersOf(Class<?> on, String method) {
        ClassDesc owner = on.describeConstable().orElseThrow();
        Set<String> found = new LinkedHashSet<>();
        for (String each : classes()) {
            ConstantPool pool = parse(each).constantPool();
            for (int i = 1; i < pool.size(); i++) {
                PoolEntry entry;
                try {
                    entry = pool.entryByIndex(i);
                } catch (Exception _) {
                    continue;
                }
                if (entry instanceof java.lang.classfile.constantpool.MemberRefEntry asCall
                        && asCall.owner().asSymbol().equals(owner)
                        && asCall.name().stringValue().equals(method)) {
                    found.add(each);
                }
            }
        }
        return found;
    }

    /** Every type {@code name} names — what it implements, calls, holds, catches or hands over. */
    public static Set<String> typesNamedBy(String name) {
        Set<String> named = new LinkedHashSet<>();
        ConstantPool pool = parse(name).constantPool();
        for (int i = 1; i < pool.size(); i++) {
            PoolEntry entry;
            try {
                entry = pool.entryByIndex(i);
            } catch (Exception _) {
                continue;
            }
            if (entry instanceof ClassEntry asClass) {
                named.add(asClass.asInternalName().replace('/', '.'));
            }
            if (entry instanceof java.lang.classfile.constantpool.Utf8Entry asText) {
                // Descriptors, which is where a field's or a parameter's type is written.
                String said = asText.stringValue();
                int at = said.indexOf('L');
                while (at >= 0) {
                    int ends = said.indexOf(';', at);
                    if (ends < 0) {
                        break;
                    }
                    named.add(said.substring(at + 1, ends).replace('/', '.'));
                    at = said.indexOf('L', ends);
                }
            }
        }
        return named;
    }

    /** {@code name} as this module compiled it, or nothing where it is not this module's — the JDK's
     *  own types and anything on the class path, which a rule about this module does not read. */
    private static ClassModel parsedOrNull(String name) {
        Path at = CLASSES.resolve(name.replace('.', '/') + ".class");
        if (!Files.exists(at)) {
            return null;
        }
        try {
            return ClassFile.of().parse(Files.readAllBytes(at));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static ClassModel parse(String name) {
        try {
            return ClassFile.of().parse(
                    Files.readAllBytes(CLASSES.resolve(name.replace('.', '/') + ".class")));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private WhatWasCompiled() {
    }
}
