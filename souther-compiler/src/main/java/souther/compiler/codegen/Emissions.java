package souther.compiler.codegen;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.JvmClassName;
import souther.compiler.jvm.SoutherJvmAbi;

import java.util.LinkedHashMap;
import java.util.Map;

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
 * are not the same question and cannot be one key: {@code Value(a.Foo)} and {@code Value(b.Foo)}
 * bridged into one module are different identities that this ABI spells the same, and keying on the
 * identity would hold both and let the JVM discover the collision at load time. So the key is the
 * spelling — collisions are detected where they exist — and what is kept under it is the identity, so
 * the report says which two things collided rather than only which name was written twice.
 */
final class Emissions {

    /** A class, and the Souther identity it was emitted for. */
    private record Emission(GeneratedClass generated, byte[] bytes) {}

    private final Map<JvmClassName, Emission> byName = new LinkedHashMap<>();

    void put(GeneratedClass generated, byte[] bytes) {
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

    /** What the compilation hands on: a class loader and a file path want the binary name, and by
     *  here every one of them came from the ABI. */
    Map<String, byte[]> byBinaryName() {
        Map<String, byte[]> out = new LinkedHashMap<>();
        byName.forEach((name, emission) -> out.put(name.binaryName(), emission.bytes()));
        return out;
    }
}
