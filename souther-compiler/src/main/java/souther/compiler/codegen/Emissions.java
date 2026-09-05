package souther.compiler.codegen;

import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.ProbeImage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.jvm.SoutherJvmAbi;

import java.lang.classfile.ClassFile;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * What a module emits: one class under one JVM name, held beside the Souther identity it was emitted
 * for.
 *
 * <p>The names a module declares and the names the compiler generates beside them are spelled into
 * one namespace, and a map takes the second write of a name as the value of it — so two classes
 * wanting one name left the artifact set short of a class, with the compile reporting nothing and the
 * loss arriving as a linkage error against whichever class went missing. The language keeps the two
 * apart by refusing {@code $} in a name (spec §identifier), and a declaration that would emit a class
 * another declaration already has is refused where it is declared (spec
 * §no-two-declarations-become-one-class). This says the same thing at the one place both are true of,
 * so a naming scheme changed later cannot bring the silence back.
 *
 * <p><b>Where the bytes stop being writable.</b> A class is built, instrumented and written onto
 * here, and all of that is one array being replaced by another. {@link #seal} is where that ends:
 * what it answers with is the classes as values, and every way of writing refuses afterwards. So the
 * one boundary between the mutable thing and the value is a call somebody makes, rather than an
 * order of statements a later stamping step can be appended after — and nothing hands out the map
 * underneath, because a caller holding that could write past the refusal.
 *
 * <p>A caller says which {@link GeneratedClass} it is emitting, not what that class is called. The two
 * are not the same question and cannot be one key: {@code BridgeCase("m", a.Foo)} and
 * {@code BridgeCase("m", b.Foo)} are different identities that this ABI spells the same, and keying on
 * the identity would hold both and let the JVM discover the collision at load time. So the key is the
 * spelling — collisions are detected where they exist — and what is kept under it is the identity, so
 * the report says which two things collided rather than only which name was written twice.
 */
public final class Emissions {

    /** A class, and the Souther identity it was emitted for. */
    private record Emission(GeneratedClass generated, byte[] bytes) {}

    private final Map<JvmClassName, Emission> byName = new LinkedHashMap<>();
    /** Which module these were emitted for, so a set with nothing of a kind in it still says whose
     *  it is. */
    private final String module;
    /** Whose numbers these classes record a run in, where they record one at all. */
    private final ProbeImage probes;
    /** What was handed out, once there is such a thing. */
    private Map<String, ClassFileImage> sealed;

    /**
     * Not public. What these classes record a run in is the generation's answer, and the way to say
     * that is that nothing outside the generation can build a set of them and put a numbering on it.
     * A caller holding the bodies can make an equal plan and an equal identity, so a public way in
     * here would be a second place the answer could come from, told apart from the first by nothing.
     */
    Emissions(String module, ProbeImage probes) {
        this.module = module;
        this.probes = Objects.requireNonNull(probes,
                "classes say whether a run through them leaves an account");
    }

    /**
     * That these are still being written, said at every way in.
     *
     * <p>What is refused is asking to write, and not a write that turned out to have something in
     * it. A guard reached only by the loop that writes an entry is a guard a caller handing over
     * nothing walks past, so what it holds is "one class was written after the sealing" — which is
     * not the rule. The rule is about the phase this is in, so it is asked of this, once per way in.
     */
    private void stillOpen(String writing) {
        if (sealed != null) {
            throw new IllegalStateException("the classes of " + module
                    + " have been handed over as values, so " + writing + " would change what a"
                    + " reader already holds; everything written onto a class is written before"
                    + " they are sealed");
        }
    }

    public void put(GeneratedClass generated, byte[] bytes) {
        stillOpen("emitting another class");
        JvmClassName name = SoutherJvmAbi.nameOf(generated);
        Emission held = byName.get(name);
        if (held != null) {
            throw new IllegalStateException("two classes were emitted as " + name + ": "
                    + held.generated() + " and " + generated
                    + "; a module's declared and generated names are one namespace and this one is"
                    + " written twice");
        }
        declares(generated, name, bytes);
        byName.put(name, new Emission(generated, bytes));
    }

    /**
     * That the class in {@code bytes} is the one this is held under.
     *
     * <p>Two walks answer where a generated class belongs: the one that made the identity, and the
     * one that built the bytes. They are the same answer, and where a walk works it out from a table
     * a spelling is the key of, they come apart — the map ships a name whose bytes declare another
     * class, so the class that was asked for is missing and the one that arrived overwrites
     * somebody else's. Nothing downstream can tell: a loader reads the name from the map.
     *
     * <p>Read here rather than left to a caller. The Class-File API hands back a model whose parts
     * are read on demand, so a read outside this method is a read outside the guard, and a name
     * nothing looked at is a name nothing checked.
     */
    private static void declares(GeneratedClass generated, JvmClassName name, byte[] bytes) {
        String written;
        try {
            written = ClassFile.of().parse(bytes).thisClass().asInternalName().replace('/', '.');
        } catch (RuntimeException e) {
            throw new IllegalStateException("the class emitted for " + generated + " as " + name
                    + " cannot be read back", e);
        }
        if (!written.equals(name.binaryName())) {
            throw new IllegalStateException("the class emitted for " + generated + " is held as "
                    + name.binaryName() + " and declares itself " + written
                    + "; a loader reads the first and the JVM reads the second, so the name asked"
                    + " for is not on the class that arrives");
        }
    }

    void putAll(Map<GeneratedClass, byte[]> classes) {
        stillOpen("emitting classes");
        classes.forEach(this::put);
    }

    /**
     * The class held for {@code generated}, rewritten. What is written onto a class after it is built
     * — a declaration, say — arrives this way rather than as a second write of its name, so a rewrite
     * of something nothing emitted is refused instead of quietly becoming the emission of it.
     *
     * <p>Held to the identity as well as to the name, for the reason the key is the name in the first
     * place: the two are not the same question. A data {@code Quote} and a behavior {@code quote} are
     * one class here, so finding a class under the name a behavior's interface has is no evidence
     * that it is that interface, and writing the behavior's declaration onto the data would leave the
     * registry saying the class had been emitted for something it was not.
     *
     * <p>What comes back keeps the identity it was emitted for. A rewrite changes what a class holds,
     * never what it is.
     */
    public void rewrite(GeneratedClass generated, java.util.function.UnaryOperator<byte[]> rewriting) {
        stillOpen("rewriting a class");
        JvmClassName name = SoutherJvmAbi.nameOf(generated);
        Emission held = byName.get(name);
        if (held == null) {
            throw new IllegalStateException("no class was emitted as " + name
                    + " for " + generated + " to carry anything");
        }
        if (!held.generated().equals(generated)) {
            throw new IllegalStateException(name + " was emitted for " + held.generated()
                    + ", not " + generated + "; one name, and not the same thing under it");
        }
        byte[] rewritten = rewriting.apply(held.bytes());
        declares(generated, name, rewritten);
        byName.put(name, new Emission(held.generated(), rewritten));
    }

    /**
     * Which behaviors this emission generated an implementation for.
     *
     * <p>The decision as it was made: a behavior is here because an implementation class was put here
     * for it, so the emitter cannot come to generate one without this saying so, or stop generating
     * one while this goes on claiming it. A set built alongside the puts would be a second record of
     * one decision, and the write that forgets to update it is the one nothing catches.
     *
     * <p>Read off the identity a class was emitted for and never off what it is called. The name a
     * behavior's implementation carries is this ABI's business and could be spelled another way
     * tomorrow, and a reader recovering behaviors from class names would be re-deriving the decision
     * from its own output — which is the thing this exists to stop.
     */
    public GeneratedImplementations implemented() {
        Set<String> behaviors = new LinkedHashSet<>();
        for (Emission emission : byName.values()) {
            if (emission.generated() instanceof GeneratedClass.BehaviorImpl impl) {
                behaviors.add(impl.behavior());
            }
        }
        return new GeneratedImplementations(module, behaviors);
    }

    /**
     * Whose numbers a run through these classes is recorded in.
     *
     * <p>The generation's own answer, and not one worked out again beside it. A numbering is made
     * from bodies, so anyone holding those bodies can make an equal one — and a report reading a run
     * back would then be trusting that two makings came to the same answer rather than reading the
     * one the probes were written from. What the emitter numbered is what the emitter says it
     * numbered.
     */
    public ProbeImage probes() {
        return probes;
    }

    /**
     * The classes as values, under the binary name each is emitted as — what the compilation hands
     * on, and the end of the writing.
     *
     * <p>By the binary name because that is what asks for a class: a loader, and a path to write it
     * at. By here every one of them came from the ABI.
     *
     * <p>Built once. Asked a second time this answers with what it answered the first time rather
     * than reading the arrays again, so what a reader was handed cannot come to differ from what
     * the next reader is handed — and an array still reachable from somewhere inside cannot reach
     * either of them.
     */
    public Map<String, ClassFileImage> seal() {
        if (sealed == null) {
            Map<String, ClassFileImage> out = new LinkedHashMap<>();
            byName.forEach((name, emission) ->
                    out.put(name.binaryName(), ClassFileImage.of(emission.bytes())));
            sealed = Collections.unmodifiableMap(out);
        }
        return sealed;
    }
}
