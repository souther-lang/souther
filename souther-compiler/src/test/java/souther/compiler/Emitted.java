package souther.compiler;

import souther.compiler.jvm.DecoderKind;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.TypeName;

/**
 * What a test reaches for when it wants a class this compiler emitted.
 *
 * <p>A test that loads {@code demo.Run$Impl} to check what a behavior computes is asserting two
 * things at once: that the behavior computes it, and that a behavior called {@code run} is emitted
 * under that name. Only the first is what such a test is for. Spelled out at every one of them, the
 * second turns a deliberate change to the ABI into a few hundred failures that all say the same
 * thing, and none of them says what changed.
 *
 * <p>So the spelling is asked for here, from the one place that decides it, and the ABI is held to
 * its spellings in exactly one test — {@code souther.compiler.jvm.SoutherJvmAbiTest} — which is
 * written against the specification rather than against this. That test and the production mapping
 * are independent, which is what makes it a check rather than a mirror.
 */
public final class Emitted {

    private Emitted() {}

    /** The class carrying a behavior's constructor and erased {@code apply}, loaded. */
    public static Class<?> behavior(ClassLoader loader, String module, String name)
            throws ClassNotFoundException {
        return GeneratedClasses.load(loader, new GeneratedClass.BehaviorImpl(module, name));
    }

    /** The interface a behavior is declared as, loaded. */
    public static Class<?> behaviorInterface(ClassLoader loader, String module, String name)
            throws ClassNotFoundException {
        return GeneratedClasses.load(loader, new GeneratedClass.BehaviorInterface(module, name));
    }

    /** The class a declared type is emitted as, loaded. */
    public static Class<?> value(ClassLoader loader, TypeName type) throws ClassNotFoundException {
        return GeneratedClasses.load(loader, new GeneratedClass.Value(type));
    }

    public static String impl(String module, String name) {
        return name(new GeneratedClass.BehaviorImpl(module, name));
    }

    public static String behaviorInterface(String module, String name) {
        return name(new GeneratedClass.BehaviorInterface(module, name));
    }

    public static String result(String module, String name) {
        return name(new GeneratedClass.BehaviorResult(module, name));
    }

    public static String bridgeCase(String emittingModule, TypeName member) {
        return name(new GeneratedClass.BridgeCase(emittingModule, member));
    }

    public static String value(String module, String type) {
        return name(new GeneratedClass.Value(new TypeName(module, type)));
    }

    public static String encoder(String module, String type) {
        return name(new GeneratedClass.Encoder(valueOf(module, type)));
    }

    public static String decoder(String module, String type, DecoderKind kind) {
        return name(new GeneratedClass.Decoder(valueOf(module, type), kind));
    }

    public static String ctfe(String module, String type) {
        return name(new GeneratedClass.Ctfe(valueOf(module, type)));
    }

    /**
     * The synthetic lambda classes {@code emitted} holds for {@code module}, in the order they were
     * numbered. Asked for by number rather than recognised by name, so a test that wants the lambdas
     * a module emitted does not need to know what one is called.
     */
    public static java.util.List<String> lambdas(java.util.Set<String> emitted, String module) {
        java.util.List<String> out = new java.util.ArrayList<>();
        for (int id = 0; ; id++) {
            String name = name(new GeneratedClass.Lambda(module, id));
            if (!emitted.contains(name)) {
                return out;
            }
            out.add(name);
        }
    }

    public static String helpers(String module) {
        return name(new GeneratedClass.Helpers(module));
    }

    public static String declarations(String module) {
        return name(new GeneratedClass.ModuleDeclarations(module));
    }

    private static GeneratedClass.Value valueOf(String module, String type) {
        return new GeneratedClass.Value(new TypeName(module, type));
    }

    private static String name(GeneratedClass generated) {
        return SoutherJvmAbi.nameOf(generated).binaryName();
    }
}
