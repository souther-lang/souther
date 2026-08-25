package souther.compiler.jvm;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeKey;

/**
 * The JVM backend's physical representation of a Souther identity: what a class is called, and what
 * a case is called where a generated class and souther-runtime pass one between them. The one place
 * that maps a Souther identity to a physical one, and the one place the suffixes and the
 * capitalization exist.
 *
 * <p>Two answers and not one. {@link #nameOf} says what a class is called; {@link #caseTokenOf} says
 * what a case is called on the wire between generated code and the runtime. They are different
 * questions and may give different answers for one identity — a declaration the runtime ships an
 * implementation for is a class in the package that ships it, while what it is a case *of* is the
 * declaration itself. Written as two methods so that neither can be reached for in place of the
 * other.
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

    /**
     * The language declarations souther-runtime ships an implementation for by hand.
     *
     * <p>Whose classification this is, said here rather than beside the declarations. That
     * {@code RoundingMode} is provided rather than generated is a fact about this backend: the
     * library declares it, and what represents it is the answer a backend gives — another one may
     * generate it and be no less right (ADR-0087, amended).
     *
     * <p>A language declaration missing from here is one nothing would emit classes for, which is a
     * fault in this compiler and is held by
     * {@code EveryLanguageDeclarationHasAJvmImplementationTest}.
     */
    private static final Map<TypeKey, JvmClassName> PROVIDED_BY_THE_RUNTIME = provided(
            "souther.decimal", "souther.runtime",
            "RoundingMode",
            "HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN", "CEILING", "FLOOR");

    /**
     * And the classes the runtime ships for the language's own cases.
     *
     * <p>A separate table because they are a separate kind of declaration: no source declares
     * {@code DivisionByZero}, so there is no address for one and nothing to key it by but the case
     * itself. {@code Some} and {@code None} are absent and stay absent — an {@code Option} match
     * dispatches on the runtime's {@code Option} classes and never on the arm's own name, so there
     * is no class for either to be called.
     */
    private static final Map<LanguageCaseId, JvmClassName> SHIPPED_LANGUAGE_CASES = Map.of(
            LanguageCaseId.DIVISION_BY_ZERO, new JvmClassName("souther.runtime.DivisionByZero"),
            LanguageCaseId.NOT_A_NUMBER, new JvmClassName("souther.runtime.NotANumber"),
            LanguageCaseId.NOT_A_DATE, new JvmClassName("souther.runtime.NotADate"),
            LanguageCaseId.NOT_A_TIME, new JvmClassName("souther.runtime.NotATime"));

    /** The same tables read backwards, for a class name arriving from outside. */
    private static final Map<String, TypeKey> DECLARED_BY_THE_RUNTIME_CLASS = inverse();

    private static Map<TypeKey, JvmClassName> provided(String declaredIn, String shippedIn,
                                                       String... names) {
        Map<TypeKey, JvmClassName> out = new LinkedHashMap<>();
        for (String name : names) {
            out.put(new TypeKey(declaredIn, name), new JvmClassName(shippedIn + "." + name));
        }
        return Collections.unmodifiableMap(out);
    }

    private static Map<String, TypeKey> inverse() {
        Map<String, TypeKey> out = new LinkedHashMap<>();
        for (Map.Entry<TypeKey, JvmClassName> e : PROVIDED_BY_THE_RUNTIME.entrySet()) {
            TypeKey already = out.put(e.getValue().binaryName(), e.getKey());
            if (already != null) {
                throw new IllegalStateException("two declarations are shipped as `"
                        + e.getValue().binaryName() + "`: " + already + " and " + e.getKey());
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /** Those, by the address the library declares each one under. */
    public static Set<TypeKey> providedByTheRuntime() {
        return PROVIDED_BY_THE_RUNTIME.keySet();
    }

    /**
     * What a declaration the language itself gives is called on the JVM.
     *
     * <p>The other half of {@link #nameOf}, for the declarations no module of a compilation makes
     * and no emission produces. The mapping happens to be the identity today — the namespace those
     * declarations are addressed under is the package souther-runtime ships them in — and that is a
     * coincidence of one backend and not a property of the name. Said here so that a second backend
     * answers the same question in its own ABI rather than reading a Souther identity as a class.
     *
     * @throws IllegalStateException where {@code name} is not one of the language's own
     */
    public static JvmClassName nameOfLanguageDeclaration(TypeSymbol name) {
        JvmClassName shipped = shippedClassOf(name);
        if (shipped == null) {
            throw new IllegalStateException(
                    "`" + name + "` is not a declaration this backend ships a class for");
        }
        return shipped;
    }

    /** Whether the runtime ships a class for {@code name} rather than anything generating one. */
    public static boolean providedByTheRuntime(TypeSymbol name) {
        return shippedClassOf(name) != null;
    }

    private static JvmClassName shippedClassOf(TypeSymbol name) {
        return switch (name) {
            case TypeSymbol.AtModule at -> PROVIDED_BY_THE_RUNTIME.get(at.key());
            case TypeSymbol.LanguageCase c -> SHIPPED_LANGUAGE_CASES.get(c.id());
            case TypeSymbol.Primitive _ -> null;
        };
    }

    /**
     * The address a class this backend ships stands for, or null where it ships none of that name.
     *
     * <p>The inverse of the table above and taken from it, so a name written out and read back
     * comes to the same declaration. What it answers is an address and not an identity: whether a
     * declaration is there is the declaration world's to say, the same as for any other class name.
     */
    public static TypeKey declarationShippedAs(String binaryName) {
        return DECLARED_BY_THE_RUNTIME_CLASS.get(binaryName);
    }

    /**
     * What {@code type} is called where a generated class and souther-runtime name a case to each
     * other: the constant an emitted comparison is written against, and the pair a
     * {@code DeclaredCase} is built from.
     *
     * <p>One answer for both, so that a comparison and the case it decides cannot come to disagree.
     * They used to be spelled at their own call sites — one from {@code qualified()} and one from
     * {@code module()} beside {@code name()} — which is two switches over the same question and two
     * places for a case added later to be handled differently.
     *
     * <p>The namespaces here are this backend's protocol and are what old jars were compiled
     * against. A case the language gives has no module, and the pair still has to say something: it
     * says what it has always said. That is a compatibility table and it lives here, which is why
     * the compiler's own model of an identity no longer carries either string.
     */
    public static RuntimeCaseToken caseTokenOf(TypeSymbol type) {
        return switch (type) {
            case TypeSymbol.AtModule at ->
                    new RuntimeCaseToken(at.key().module(), at.key().name());
            case TypeSymbol.Primitive p -> new RuntimeCaseToken("souther", p.name());
            case TypeSymbol.LanguageCase c -> switch (c.id()) {
                case SOME, NONE -> new RuntimeCaseToken("souther", c.name());
                case DIVISION_BY_ZERO, NOT_A_NUMBER, NOT_A_DATE, NOT_A_TIME ->
                        new RuntimeCaseToken("souther.runtime", c.name());
            };
        };
    }

    /** What {@code generated} is called on the JVM. */
    public static JvmClassName nameOf(GeneratedClass generated) {
        return new JvmClassName(switch (generated) {
            // A declaration the runtime ships is called what it is called there, which is not
            // where the library declares it. Every other value class is its type's own address,
            // the module being the package.
            case GeneratedClass.Value v -> valueClassName(v.type());
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
            case GeneratedClass.Ensures e -> nameOf(e.of()).binaryName() + "$Ensures";
            case GeneratedClass.ModuleDeclarations m -> m.module() + ".$Module";
            case GeneratedClass.Helpers h -> h.module() + ".$Fns";
            case GeneratedClass.Lambda l -> l.module() + ".$Fn" + l.id();
        });
    }

    /**
     * What a value of {@code type} is called.
     *
     * <p>A declaration the runtime ships is called what it is called there, which is not where the
     * library declares it. Every other value class is its type's own address, the module being the
     * package. A primitive is neither: a value of one is carried as its boxed class and never as a
     * class of this compiler's, so asking for one is a caller that took a scalar for a declaration.
     */
    private static String valueClassName(TypeSymbol type) {
        JvmClassName shipped = shippedClassOf(type);
        if (shipped != null) {
            return shipped.binaryName();
        }
        if (type instanceof TypeSymbol.AtModule at) {
            return at.key().qualified();
        }
        throw new IllegalStateException("`" + type + "` is no value class of this backend");
    }

    /**
     * The address whose {@code Value} identity would have this binary name, or null where no type's
     * would. It says nothing about whether such a type is declared, or about what was really emitted
     * under the name.
     *
     * <p>The naming rule for a value class run backwards, and the only rule here that can be: a value
     * class is its type, so the two directions are one rule. Every other kind either adds something
     * to a name or shares one with a kind that does — {@code demo.Quote} is a data {@code Quote} and
     * it is also the interface of a behavior {@code quote} — so a name alone does not say which, and
     * asking is the only way.
     *
     * <p>Which is why it answers a {@link TypeKey} and not a {@link TypeSymbol}. An address is what a
     * class file carries and a query is asked with; it becomes an identity where a declaration world
     * says a declaration is there, which is what the caller does with this
     * ({@code symbols.declarations().identify(candidate)}). An ABI that answered an identity would be
     * claiming a declaration it has no way to see.
     */
    public static TypeKey valueTypeCandidate(String binaryName) {
        TypeKey shipped = declarationShippedAs(binaryName);
        if (shipped != null) {
            return shipped;
        }
        int dot = binaryName.lastIndexOf('.');
        if (dot <= 0 || dot == binaryName.length() - 1) {
            return null;
        }
        return new TypeKey(binaryName.substring(0, dot), binaryName.substring(dot + 1));
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
