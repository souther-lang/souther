package souther.compiler.codegen;

import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.jvm.SoutherJvmAbi;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
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

    public Emissions(String module) {
        this.module = module;
    }

    public void put(GeneratedClass generated, byte[] bytes) {
        JvmClassName name = SoutherJvmAbi.nameOf(generated);
        Emission held = byName.get(name);
        if (held != null) {
            throw new IllegalStateException("two classes were emitted as " + name + ": "
                    + held.generated() + " and " + generated
                    + "; a module's declared and generated names are one namespace and this one is"
                    + " written twice");
        }
        byName.put(name, new Emission(generated, bytes));
    }

    void putAll(Map<GeneratedClass, byte[]> classes) {
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
        byName.put(name, new Emission(held.generated(), rewriting.apply(held.bytes())));
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

    /** What the compilation hands on: a class loader and a file path want the binary name, and by
     *  here every one of them came from the ABI. */
    public Map<String, byte[]> byBinaryName() {
        Map<String, byte[]> out = new LinkedHashMap<>();
        byName.forEach((name, emission) -> out.put(name.binaryName(), emission.bytes()));
        return out;
    }
}
