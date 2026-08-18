package souther.compiler.check;

import souther.compiler.ast.WrittenName;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What a type name written in this module means here.
 *
 * <p>Everything about "here": what a bare spelling denotes, which module a qualifier names, what an
 * alias reaches, how a type is written back. A spelling means something in the module that wrote it,
 * so a spelling never reaches this from anywhere else, and nothing that takes an identity belongs on
 * it — {@link Declarations} answers what an identity is a declaration of, and does not need to know
 * which module is asking.
 *
 * <p>The two used to be one object holding both, and which of them a reader was asking was
 * something it worked out for itself: a spelling nothing here writes and a declaration that did not
 * come out are different absences, and reading one for the other is how a name came to be answered
 * against the wrong module.
 *
 * <p>Not {@link Scope}, which is what a body may name where an expression is being typed. That one
 * is about a position inside a definition; this one is about the module.
 *
 * <p>Reads {@link Registry} for what other modules expose and for which modules there are, which are
 * facts about them rather than about here. It does not read declarations: a qualified name is
 * answered against what this compilation declares, so that the language\'s own vocabulary —
 * reachable bare and under no qualifier — cannot be reached through one.
 */
public final class TypeScope {

    private final String module;
    /** What a name written here means: this module\'s own definitions plus the imported ones, and
     * what each {@code import ... as} alias reaches. Asked rather than held, for the reason
     * {@link Denoting} gives.
     *
     * <p>Not every qualifier is an alias. A module of the compilation is one under its own name,
     * which {@link #moduleOfQualifier} reads off the registry — listed here instead, a scope could
     * not be built without naming every module of the compilation up front. */
    private final Denoting names;
    private final Registry<?> registry;

    TypeScope(String module, Denoting names, Registry<?> registry) {
        this.module = module;
        this.names = names;
        this.registry = registry;
    }

    /** The module being compiled. */
    public String module() {
        return module;
    }

    /**
     * What a written case name denotes. Beside the data cases a module declares or imports, an arm may
     * name a case of a primitive-headed union: the primitive itself ({@code Int} in {@code Int |
     * DivisionByZero}), or one of the error cases the runtime declares rather than any module. Null
     * when it is none of those.
     */
    Denotation resolveCase(WrittenName written) {
        return switch (written.canonical()) {
            case "Int", "String", "Bool", "Decimal", "Date", "Time", "DateTime", "Instant", "Raw" ->
                    new Denotation.Denotes(TypeSymbol.primitive(written.canonical()));
            case "DivisionByZero", "NotANumber", "NotADate", "NotATime" ->
                    new Denotation.Denotes(TypeSymbol.runtime(written.canonical()));
            default -> resolve(written);
        };
    }

    /** What the written name {@code written} denotes here. Accepts a bare name, a
     * module-qualified one ({@code probe.b.金額}) and an alias-qualified one ({@code B.金額}).
     * Visibility is enforced: a qualified name must be exposed by the module that declares it.
     *
     * <p>"Here" is the whole story: a name is resolved in the module that wrote it, by that module's
     * own {@link Resolve} pass, so this never has to answer for a spelling written somewhere else.
     */
    Denotation resolve(WrittenName written) {
        return resolveSpelling(written.canonical());
    }

    /** As above, of the spelling itself. Private: a spelling reaches this only from a name of this
     *  module's own text, which is what a {@link WrittenName} is and a bare string is not. */
    private Denotation resolveSpelling(String written) {
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            Denotation name = names.of(written);
            if (!(name instanceof Denotation.NotInScope)) {
                return name;
            }
            // The prelude's runtime-backed data is nameable everywhere, on the lowest rung: a
            // module's own declaration or import of the same name is what the name means there.
            TypeSymbol runtime = Prelude.runtimeBackedType(written);
            return runtime != null ? new Denotation.Denotes(runtime) : Denotation.NOT_IN_SCOPE;
        }
        String target = moduleOfQualifier(written.substring(0, dot));
        if (target == null) {
            return Denotation.NOT_IN_SCOPE;
        }
        String bare = written.substring(dot + 1);
        // Asked rather than assembled: an address is not an identity until something declares one
        // there, and what comes back is that identity or nothing.
        TypeSymbol denoted = registry.identify(new TypeKey(target, bare));
        return denoted != null && exposes(target, bare)
                ? new Denotation.Denotes(denoted) : Denotation.NOT_IN_SCOPE;
    }

    /** Whether {@code name} is declared in another module (spec §modules). */
    public boolean isForeign(TypeSymbol name) {
        return !name.module().equals(module);
    }

    /**
     * How this module writes {@code type} — the one thing a writer of surface text cannot work out
     * from the type itself.
     *
     * <p>A section of {@link #resolve} rather than its inverse. Several spellings reach one
     * declaration — {@code Amount}, {@code up.Amount} and {@code lib.Amount} may all be it — so
     * there is no inverse to have; this picks one of them, and what it picks resolves back to the
     * type it was asked about. That is the whole of the contract, and it is what a generated row
     * being writable means.
     *
     * <p>Read back by whichever reader reads the position the name is written at, which for the
     * language's own vocabulary is not this one: a primitive and the runtime's error cases are
     * {@link #resolveCase}'s to answer, and {@code resolve} says nothing about them. They are
     * written as themselves wherever they are written, so the section holds there through that
     * reader.
     *
     * <p>Bare only where the bare spelling means this very declaration. Asked as "is the name in
     * scope" instead, a module that declares an {@code Amount} of its own and reaches another
     * module's under an alias would write the imported one bare, and the reference would name the
     * declaration it is not — silently, since both spellings resolve.
     *
     * <p>An alias is chosen by name where a module has more than one, so that two runs of the same
     * compilation write one reference. Nothing here picks the alias for being better than the
     * others; it picks it for being the same one every time.
     *
     * <p>So a bare name is answered only where the bare name means this type <em>here</em>, and
     * that is one question for every kind of type. A primitive's spelling is reserved (E1502), so
     * nothing can be standing on it. The runtime namespace's own data is not reserved and is the
     * lowest rung of a module's scope — a module declaring a {@code RoundingMode} of its own takes
     * the spelling, and the language's one has no other, so it is unnameable there rather than bare
     * (ADR-0087).
     *
     * <p>A qualified name reaches only what its module exposes, so a type another module keeps to
     * itself has no name here at all. That happens without anything being wrong with the model: a
     * sum is reached through its module and its cases through the sum, so a case a module does not
     * expose is a value a reader takes and cannot write. It is answered as
     * {@link TypeReachName.Unnameable} rather than as the qualified spelling, which would resolve to
     * nothing wherever it was put.
     */
    public TypeReachName reach(TypeSymbol type) {
        if (type.isPrimitive() || type.equals(names.of(type.name()) instanceof Denotation.Denotes d
                ? d.type() : null)) {
            return new TypeReachName.Bare(type);
        }
        if (TypeSymbol.RUNTIME.equals(type.module())) {
            // Reached bare, and only while nothing else here is: the runtime namespace is not a
            // module a qualifier names, so a module declaring the spelling leaves it with no name.
            return inScope(type.name()) ? new TypeReachName.Unnameable(type)
                    : new TypeReachName.Bare(type);
        }
        if (!exposes(type.module(), type.name())) {
            return new TypeReachName.Unnameable(type);
        }
        String alias = null;
        for (String each : names.aliases()) {
            if (type.module().equals(names.moduleOfAlias(each))
                    && (alias == null || each.compareTo(alias) < 0)) {
                alias = each;
            }
        }
        return alias != null ? new TypeReachName.ViaAlias(alias, type)
                : new TypeReachName.ViaModule(type);
    }

    /**
     * The module of this compilation that exposes {@code name}, or null where that is not exactly
     * one module.
     *
     * <p>Asked where a bare name resolved to nothing, so that a name left off an import list is told
     * apart from a name nothing declares. This module is not among them: what it declares is already
     * in scope, so reaching here means it does not.
     *
     * <p>Exactly one, because the answer is written into a report as the module to reach for. Two
     * modules exposing the spelling makes naming either one a guess, and a guess in a hint is worse
     * than the silence it replaces — the reader is already being told the name is not in scope.
     */
    public String moduleExposing(String name) {
        String found = null;
        for (String other : new java.util.TreeSet<>(registry.moduleNames())) {
            if (other.equals(module) || !registry.exposedBy(other).contains(name)) {
                continue;
            }
            if (found != null) {
                return null;
            }
            found = other;
        }
        return found;
    }

    /** The module a qualifier names — a module of this compilation, or an import alias — or null
     * when it names none. Used to tell "unknown module" apart from "unknown type in a known
     * module". */
    public String moduleOfQualifier(String qualifier) {
        String alias = names.moduleOfAlias(qualifier);
        if (alias != null) {
            return alias;
        }
        return registry.moduleNames().contains(qualifier) ? qualifier : null;
    }

    /** Every qualifier a reference may carry here — what a "did you mean" may offer for one. */
    public Set<String> qualifiers() {
        Set<String> all = new LinkedHashSet<>(registry.moduleNames());
        all.addAll(names.aliases());
        return all;
    }

    /** Whether {@code name} is reachable here as a bare name. */
    public boolean inScope(String name) {
        return !(names.of(name) instanceof Denotation.NotInScope);
    }

    /** The bare names reachable here — what a "did you mean" suggestion may offer. */
    public Set<String> namesInScope() {
        return names.spellings();
    }

    /**
     * Every bare spelling that reaches a name here, and the name it reaches.
     *
     * <p>The pair, which is what resolving a name answers. A spelling in scope standing for nothing
     * is not here — it reaches no name — and it is still reachable, which {@link #namesInScope}
     * answers. Two absences, two questions: whether a spelling may be written is the second, and
     * what writing it would mean is this one.
     */
    public Map<String, TypeSymbol> denotedNames() {
        Map<String, TypeSymbol> named = new LinkedHashMap<>();
        for (String spelling : names.spellings()) {
            if (names.of(spelling) instanceof Denotation.Denotes d) {
                named.put(spelling, d.type());
            }
        }
        return named;
    }

    /** The names reachable here, canonical. A name in scope standing for nothing names no
     * declaration, so it is reachable and not among these. */
    public Collection<TypeSymbol> visibleNames() {
        return new LinkedHashSet<>(denotedNames().values());
    }

    /** Whether the module that declares {@code name} exposes it — its own names always count. */
    public boolean isExposed(TypeSymbol name) {
        return exposes(name.module(), name.name());
    }

    /** Whether {@code moduleName} exposes {@code name} (dropping any {@code .decoder} member). */
    private boolean exposes(String moduleName, String name) {
        if (moduleName.equals(module)) {
            return true;   // a module reaches its own definitions whether it exposes them or not
        }
        return registry.exposedBy(moduleName).contains(name);
    }
}
