package souther.compiler.jvm;

import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

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
     * The {@link TypeSymbol} whose {@code Value} identity would have this binary name, or null where no
     * type's would. It says nothing about whether such a type is declared, or about what was really
     * emitted under the name.
     *
     * <p>The naming rule for a value class run backwards, and the only rule here that can be: a value
     * class is its type, so the two directions are one rule. Every other kind either adds something
     * to a name or shares one with a kind that does — {@code demo.Quote} is a data {@code Quote} and
     * it is also the interface of a behavior {@code quote} — so a name alone does not say which, and
     * asking is the only way.
     *
     * <p>Which is why this answers half a question and is named for its half. Whether a type is
     * there is a module's scope to answer, and the caller that has one asks it:
     * {@code candidate != null && symbols.declarations().contains(candidate.key())}. An ABI that answered both would be
     * claiming a declaration it has no way to see — the same shape as an authority that hands out
     * half an answer, pointed the other way.
     */
    public static TypeSymbol valueTypeCandidate(String binaryName) {
        int dot = binaryName.lastIndexOf('.');
        if (dot <= 0 || dot == binaryName.length() - 1) {
            return null;
        }
        return TypeSymbols.recovered(
                new TypeKey(binaryName.substring(0, dot), binaryName.substring(dot + 1)));
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
