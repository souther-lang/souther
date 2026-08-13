package souther.compiler.jvm;

/**
 * How a {@link GeneratedClass} is spelled on the JVM. The one place that maps a Souther identity to a
 * physical one, and the one place the suffixes and the capitalization exist.
 *
 * <p>{@link #nameOf} is a switch expression over a sealed interface with no default, so a generated
 * class this ABI has no answer for is a compile error rather than a name assembled somewhere else.
 * Adding a kind of emitted class and forgetting to say what it is called is the shape that cannot
 * happen here.
 *
 * <p>The mapping is not injective and is not meant to be. A data {@code Quote} and a behavior
 * {@code quote} are two identities that land on {@code m.Quote}; that they collide is a fact about
 * this ABI and is refused where a module is emitted (see {@code Backend} and its emission registry),
 * not hidden here.
 */
public final class SoutherJvmAbi {

    private SoutherJvmAbi() {}

    /** What {@code generated} is called on the JVM. */
    public static JvmClassName nameOf(GeneratedClass generated) {
        return new JvmClassName(switch (generated) {
            case GeneratedClass.Value v -> v.type().qualified();
            case GeneratedClass.BehaviorInterface b -> b.module() + "." + capitalized(b.behavior());
            case GeneratedClass.BehaviorImpl b -> b.module() + "." + capitalized(b.behavior()) + "$Impl";
            case GeneratedClass.BehaviorResult b -> b.module() + "." + capitalized(b.behavior()) + "Result";
            case GeneratedClass.BridgeCase c -> c.emittingModule() + "." + c.member().name() + "Case";
            case GeneratedClass.Encoder e -> nameOf(e.of()).binaryName() + "$Enc";
            case GeneratedClass.Decoder d -> nameOf(d.of()).binaryName() + switch (d.kind()) {
                case VALUE -> "$Dec";
                case JSON -> "$DecJson";
                case RECORD -> "$DecRecord";
            };
            case GeneratedClass.Ctfe c -> nameOf(c.of()).binaryName() + "$Ctfe";
            case GeneratedClass.ExampleFake f -> nameOf(f.of()).binaryName() + "$Fake";
            case GeneratedClass.ModuleDeclarations m -> m.module() + ".$Module";
            case GeneratedClass.Helpers h -> h.module() + ".$Fns";
            case GeneratedClass.Lambda l -> l.module() + ".$Fn" + l.id();
        });
    }

    /**
     * A behavior's name with its first letter capitalized (spec §jvm-behavior). A Japanese leading
     * character has no upper-case form, so a Japanese-named behavior is emitted unchanged. The
     * behavior's name stays lower-case wherever it is an identity — an injected field name, a
     * requirement-set entry, a signature-map key — and only the emitted class name is capitalized.
     */
    private static String capitalized(String behavior) {
        return Character.toUpperCase(behavior.charAt(0)) + behavior.substring(1);
    }
}
