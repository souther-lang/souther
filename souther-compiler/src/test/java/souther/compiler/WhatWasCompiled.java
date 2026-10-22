package souther.compiler;

import souther.test.CompiledClasses;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.ConstantPool;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.MethodTypeEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.constant.ClassDesc;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What this module compiled to, for a rule about who may depend on what.
 *
 * <p>A structural rule read off the source reads the spellings that are there today. "A file saying
 * {@code implements X}" is not the set of things that answer {@code X} — a lambda answers one and
 * says neither word, and the next one to get this wrong will be written the way the last one was
 * not. So the set is taken from what javac made of the module, where an anonymous body, a class and
 * a lambda are all present and all say what they are.
 *
 * <p>Read from what this module compiled to, which is what surefire was handed and what the tests
 * using this were compiled against. Which output that is, and how many times its files are opened,
 * are {@link CompiledClasses}'s to answer; what is here is what this module's rules ask of it.
 */
public final class WhatWasCompiled {

    /**
     * What this module compiled, named in one place.
     *
     * <p>A check of this module asks about this module, and a check that named the output for
     * itself would be one more place to get it wrong when a module moves.
     */
    public static CompiledClasses compiled() {
        return COMPILED;
    }

    /**
     * The checks compiled beside it, which is the other output this module has.
     *
     * <p>Here for the same reason the one above is: a rule about the checks themselves is a rule
     * about an output of this module, and naming it somewhere else would be a second place saying
     * where this module's classes are.
     */
    public static CompiledClasses checksCompiledBesideIt() {
        return BESIDE;
    }

    /**
     * Which output this module compiled to, worked out once.
     *
     * <p>Not the classes, which the fork holds: this is the view of them, and working one out asks
     * the file system what the path it was handed really is. A rule that walks the supertypes of
     * every class asks for the view once per name it follows, so working it out per ask is a system
     * call per lookup for an answer that was the same every time.
     */
    private static final CompiledClasses COMPILED = CompiledClasses.ofModule(Compiler.class);

    private static final CompiledClasses BESIDE = CompiledClasses.ofModule(WhatWasCompiled.class);

    /** Every class this module compiled, by binary name and without reading any of them. */
    public static List<String> classes() {
        return compiled().names();
    }

    private static String named(ClassModel of) {
        return of.thisClass().asInternalName().replace('/', '.');
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
        Set<String> isOne = kinds().getOrDefault(asked, Set.of());
        Set<String> found = new LinkedHashSet<>();
        for (ClassModel each : compiled().all()) {
            String name = named(each);
            if (isOne.contains(name) || lambdaOf(each, asked)) {
                found.add(name);
            }
        }
        return found;
    }

    /**
     * Every class that <em>is</em> an {@code answered}, through however many types in between.
     *
     * <p>Narrower than {@link #answering} and for a different question: how many things of a kind
     * there are, rather than which files write one. A rule about what an answer may depend on is
     * about the file that wrote it, and a lambda's file is where it was written; a count of the
     * answers themselves must not take a file that merely hands one back for one more of them.
     *
     * <p>Complete only for an interface a lambda cannot answer. Ask that of the interface where the
     * count is read, because an interface that becomes functional makes this go blind rather than
     * wrong.
     */
    public static Set<String> implementing(Class<?> answered) {
        ClassDesc asked = answered.describeConstable().orElseThrow();
        return new LinkedHashSet<>(kinds().getOrDefault(asked, Set.of()));
    }

    /**
     * Every type each compiled class is, through however many types in between, turned round: for
     * each type, the compiled classes that are one, in the order the classes are listed.
     *
     * <p>Directly or not. An interface between the two is a way of answering it and not a way of
     * not answering it, and a rule reading only the interfaces named on the class itself would let
     * one through for the length of one declaration.
     *
     * <p>Read once, because it is one fact about the output: asked type by type, the supertypes of
     * every class were followed again for each type asked about.
     */
    private static Map<ClassDesc, Set<String>> kinds() {
        Map<ClassDesc, Set<String>> read = kinds;
        if (read != null) {
            return read;
        }
        synchronized (WhatWasCompiled.class) {
            if (kinds == null) {
                Map<String, Set<ClassDesc>> above = new HashMap<>();
                Map<ClassDesc, Set<String>> out = new HashMap<>();
                for (ClassModel each : compiled().all()) {
                    String name = named(each);
                    for (ClassDesc type : typesAbove(each, above)) {
                        out.computeIfAbsent(type, _ -> new LinkedHashSet<>()).add(name);
                    }
                }
                kinds = out;
            }
            return kinds;
        }
    }

    private static volatile Map<ClassDesc, Set<String>> kinds;

    /**
     * Every type {@code model} is, other than itself: what it extends and implements, and what
     * each of those that this module compiled is in turn. A type this module did not compile is
     * where the walk stops.
     *
     * @param known what was found of the classes already walked, by name
     */
    private static Set<ClassDesc> typesAbove(ClassModel model, Map<String, Set<ClassDesc>> known) {
        String name = named(model);
        Set<ClassDesc> found = known.get(name);
        if (found != null) {
            return found;
        }
        known.put(name, Set.of());
        Set<ClassDesc> out = new LinkedHashSet<>();
        List<ClassDesc> direct = new ArrayList<>();
        model.superclass().ifPresent(each -> direct.add(each.asSymbol()));
        model.interfaces().forEach(each -> direct.add(each.asSymbol()));
        for (ClassDesc each : direct) {
            out.add(each);
            compiled().find(each.packageName().isEmpty()
                            ? each.displayName()
                            : each.packageName() + "." + each.displayName())
                    .ifPresent(further -> out.addAll(typesAbove(further, known)));
        }
        known.put(name, out);
        return out;
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
     * <p>For a rule about who may do something rather than about who may name a type. A lambda's
     * body is compiled into the class that wrote it, so a caller cannot get out of this by writing
     * the call somewhere shorter.
     *
     * <p><b>Through whatever type it is named.</b> What a call site puts in the constant pool is
     * the type the receiver was declared as, so a method of an interface called through one of its
     * implementations is a reference to the implementation. A rule about who may do something is
     * about the operation and not about the spelling of the variable it was reached through, and a
     * rule reading only the type it was asked about would be escaped by declaring the receiver one
     * step down. So the owners are that type and every compiled type that answers it
     * ({@link #implementing}).
     *
     * <p>A type this module did not compile has no implementations to gather, and the walk over
     * what it did compile finds none — which is the right answer for a rule about this module's own
     * calls into somebody else's type.
     */
    public static Set<String> callersOf(Class<?> on, String method) {
        Set<ClassDesc> owners = new LinkedHashSet<>();
        owners.add(on.describeConstable().orElseThrow());
        for (String each : implementing(on)) {
            owners.add(ClassDesc.of(each));
        }
        Map<ClassDesc, Set<String>> byOwner = callsByName().getOrDefault(method, Map.of());
        Set<String> found = new TreeSet<>();
        for (ClassDesc owner : owners) {
            found.addAll(byOwner.getOrDefault(owner, Set.of()));
        }
        return found;
    }

    /**
     * Every member each compiled class refers to, by the member's name and then its owner, and the
     * classes that refer to it: what the compiled classes say about who calls what, read once.
     *
     * <p>Once because it is one fact about the output, and asked of it member by member the same
     * pool of every class was read again for each member asked about.
     */
    private static Map<String, Map<ClassDesc, Set<String>>> callsByName() {
        Map<String, Map<ClassDesc, Set<String>>> read = calls;
        if (read != null) {
            return read;
        }
        synchronized (WhatWasCompiled.class) {
            if (calls == null) {
                Map<String, Map<ClassDesc, Set<String>>> out = new HashMap<>();
                for (ClassModel model : compiled().all()) {
                    ConstantPool pool = model.constantPool();
                    for (int i = 1; i < pool.size(); i++) {
                        PoolEntry entry;
                        try {
                            entry = pool.entryByIndex(i);
                        } catch (Exception _) {
                            continue;
                        }
                        if (entry instanceof MemberRefEntry asCall) {
                            out.computeIfAbsent(asCall.name().stringValue(), _ -> new HashMap<>())
                                    .computeIfAbsent(asCall.owner().asSymbol(),
                                            _ -> new LinkedHashSet<>())
                                    .add(named(model));
                        }
                    }
                }
                calls = out;
            }
            return calls;
        }
    }

    private static volatile Map<String, Map<ClassDesc, Set<String>>> calls;

    /**
     * {@code named} and every compiled type that is one, however many types in between.
     *
     * <p>For a rule about values of a kind rather than about one spelling of it. A term arrives
     * under the name of its case as readily as under its own, and a set written as "the name, or
     * anything whose name begins with it and a dollar" is a guess about spelling that takes in a
     * type merely written inside one — where what makes a value answer for the kind is being one.
     */
    public static Set<String> everyKindOf(String named) {
        Set<String> found = new LinkedHashSet<>();
        found.add(named);
        found.addAll(kinds().getOrDefault(ClassDesc.of(named), Set.of()));
        return found;
    }

    /**
     * Every type {@code name} names — what it implements, calls, holds, catches or hands over.
     *
     * <p>Read once for each class, since the class does not change while the fork holds it, and a
     * census of every class asks it of each of them.
     */
    public static Set<String> typesNamedBy(String name) {
        return NAMED.computeIfAbsent(name, each -> Collections.unmodifiableSet(readNamedBy(each)));
    }

    private static final Map<String, Set<String>> NAMED = new ConcurrentHashMap<>();

    private static Set<String> readNamedBy(String name) {
        Set<String> named = new LinkedHashSet<>();
        ConstantPool pool = compiled().find(name)
                .orElseThrow(() -> new IllegalArgumentException(
                        name + " is not a class this module compiled"))
                .constantPool();
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
                // Descriptors, which is where a field's or a parameter's type is written, and
                // signatures, which is where a type argument is. A name ends at the `;` that closes
                // it or at the `<` that opens what it was given, and reading to the `;` alone made
                // `List<Foo>` one name of its own — so the type a collection was of was named
                // nowhere, and a rule about who may name what was blind to exactly the spelling
                // that hides one.
                String said = asText.stringValue();
                int at = said.indexOf('L');
                while (at >= 0) {
                    int ends = at + 1;
                    while (ends < said.length() && said.charAt(ends) != ';'
                            && said.charAt(ends) != '<') {
                        ends++;
                    }
                    if (ends >= said.length()) {
                        break;
                    }
                    named.add(said.substring(at + 1, ends).replace('/', '.'));
                    at = said.indexOf('L', ends);
                }
            }
        }
        return named;
    }

    private WhatWasCompiled() {
    }
}
