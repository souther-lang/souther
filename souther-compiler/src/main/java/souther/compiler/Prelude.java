package souther.compiler;

import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.ast.Ast;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.check.TypeOps;
import souther.compiler.frontend.CstFrontend;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The standard library the compiler ships in the reserved {@code souther} namespace (ADR-0028,
 * spec §reserved-namespace). Its modules are packaged as resources and parsed once, into one
 * {@linkplain #entry(String) entry} per qualified name: the declaration as it was written and its
 * resolved signature. What is behind the name — a Souther body, expanded inline at each call site
 * (see {@code check.HelperInliner}), or a named kernel the backend emits — is the declaration's
 * {@linkplain Ast.FnBody body}, not a second registry.
 *
 * <p>Everything is reached through a module qualifier — {@code List.map}, {@code String.trim} — since
 * the standard library carries no bare names (spec §stdlib). Entries are therefore keyed by their
 * qualified name.
 */
public final class Prelude {

    /** The bundled prelude sources, in load order. */
    private static final List<String> RESOURCES =
            List.of("/souther/bool.sou", "/souther/string.sou", "/souther/map.sou", "/souther/list.sou",
                    "/souther/set.sou", "/souther/date.sou", "/souther/datetime.sou",
                    "/souther/int.sou", "/souther/decimal.sou", "/souther/option.sou");

    /** Reserved module name → short qualifier (spec §stdlib). {@code souther.list} → {@code List}. */
    private static final Map<String, String> MODULE_TO_ALIAS = Map.ofEntries(
            Map.entry("souther.list", "List"),
            Map.entry("souther.string", "String"),
            Map.entry("souther.map", "Map"),
            Map.entry("souther.set", "Set"),
            Map.entry("souther.bool", "Bool"),
            Map.entry("souther.date", "Date"),
            Map.entry("souther.datetime", "DateTime"),
            Map.entry("souther.int", "Int"),
            Map.entry("souther.decimal", "Decimal"),
            Map.entry("souther.option", "Option"));

    /** Every qualifier a call may carry — the language's constant ({@link Reserved}), read from
     *  there so nothing has to initialize this class to know it. */
    private static final Set<String> QUALIFIERS = Reserved.QUALIFIERS;

    /** A declaration's resolved signature: its parameter types, and the success type of its declared
     *  return — or null where the declaration writes no return type and leaves its result to its
     *  body, which a Souther-bodied helper with parameters may and a kernel never does. A
     *  zero-parameter declaration is a value and always has a result here (see
     *  {@link #signatureOf}). Resolved once at load; what the failure cases of the return are is the
     *  checker's question about the call, not the signature's. */
    public record Signature(List<Type> params, Type result) {
        public Signature {
            params = List.copyOf(params);
        }
    }

    /** Everything the library says under one qualified name: the {@code let} as it was written and
     *  its resolved signature. Existence, declaration, signature and implementation are one answer —
     *  a reader takes the projection it wants rather than picking a map. */
    public record PreludeEntry(Ast.FnDef declaration, Signature signature) {
    }

    /** Every declaration the library ships, keyed by qualified name ({@code "List.map"}). */
    private static final Map<String, PreludeEntry> ENTRIES = new LinkedHashMap<>();

    /**
     * The data declarations whose JVM implementation souther-runtime provides by hand rather than
     * the backend generating. The classification is made once, here: it anchors the declared names
     * to the runtime namespace ({@code souther.runtime.RoundingMode} is the class shipped there),
     * answers {@link Symbols}' lookups for them, and — because the declarations belong to no
     * compiled module — keeps them out of derivation and code generation, which is why such a data
     * has no codec. A prelude data not registered here is refused at load: nothing would emit its
     * classes.
     */
    private static final Set<String> RUNTIME_BACKED_DATA = Set.of("RoundingMode");

    /** The resolved runtime-backed declarations — the sums and their cases — keyed by bare name. */
    private static final Map<String, Ast.Def> RUNTIME_DEFS = new LinkedHashMap<>();

    /** Each kernel's declared signature, keyed by its intrinsic key ({@code "decimal.toInt"}) —
     *  the projection of {@link #ENTRIES} the backend reads to derive a kernel's JVM descriptor
     *  from the declaration rather than repeating it. */
    private static final Map<String, Signature> KERNELS = new LinkedHashMap<>();

    /** Bare stdlib name → a qualified suggestion, so a bare call gets a "did you mean" hint. The
     *  checker built-ins (which are not in the prelude sources) are listed here explicitly. */
    private static final Map<String, String> BARE_TO_QUALIFIED = new LinkedHashMap<>();

    /** The Souther-bodied declarations, as the inliner's table wants them: a materialized projection
     *  of {@link #ENTRIES}, derived once after loading and never written again. */
    private static final Map<String, Ast.FnDef> HELPERS;

    static {
        load();
        Map<String, Ast.FnDef> helpers = new LinkedHashMap<>();
        for (Map.Entry<String, PreludeEntry> e : ENTRIES.entrySet()) {
            if (e.getValue().declaration().body() instanceof Ast.FnBody.Written) {
                helpers.put(e.getKey(), e.getValue().declaration());
            }
        }
        HELPERS = Collections.unmodifiableMap(helpers);
    }

    private Prelude() {
    }

    /** Whether {@code qualifier} names a standard-library namespace a call/import may use:
     *  {@code List}/{@code String}/{@code Map}/{@code Bool}/{@code Int}/{@code Decimal} (spec §stdlib). */
    public static boolean isQualifier(String qualifier) {
        return QUALIFIERS.contains(qualifier);
    }

    /** Every standard-library qualifier ({@code List} / {@code Map} / … / {@code Option}). The
     *  syntax highlighter derives its qualifier list from this so the two never drift apart. */
    public static Set<String> qualifiers() {
        return QUALIFIERS;
    }

    /** Names that are sugar for another standard-library call, recognised as library functions but
     *  rewritten before inlining: {@code List.fold(step, seed, xs)} is {@code List.foldFrom(step, seed,
     *  xs, 0)} (the walk from the head). */
    private static final Set<String> SUGARED = Set.of("List.fold");

    /** Whether {@code qualifiedName} is one of those — a name no tree holds after the rewrite, so a
     *  rule keyed by it can never be looked up (see {@code InvariantChecker}'s combinator table). */
    public static boolean sugared(String qualifiedName) {
        return SUGARED.contains(qualifiedName);
    }

    /** Whether {@code qualifiedName} (e.g. {@code "List.map"}) is a standard-library function — a
     *  declared one, or a sugar for one. Sugar has no declaration of its own, so this is wider than
     *  {@link #entry(String)} answering: {@code List.fold} is a library function and has no entry. */
    public static boolean isLibraryFunction(String qualifiedName) {
        return ENTRIES.containsKey(qualifiedName) || SUGARED.contains(qualifiedName);
    }

    /** The library's entry for {@code qualifiedName}, or null where the library declares no such
     *  name — including for {@linkplain #sugared(String) sugar}, which is a rewrite, not a
     *  declaration. */
    public static PreludeEntry entry(String qualifiedName) {
        return ENTRIES.get(qualifiedName);
    }

    /** Every entry, keyed by qualified name, in declaration order. */
    public static Map<String, PreludeEntry> entries() {
        return Collections.unmodifiableMap(ENTRIES);
    }

    /** The Souther-bodied declarations (inlined at call sites), keyed by qualified name, in
     *  declaration order. */
    public static Map<String, Ast.FnDef> helpers() {
        return HELPERS;
    }

    /** A qualified suggestion for a bare standard-library name ({@code "map"} → {@code "List.map"}),
     *  or {@code null} if the name is not a standard-library function. */
    public static String qualifiedFor(String bareName) {
        return BARE_TO_QUALIFIED.get(bareName);
    }

    private static void load() {
        for (String resource : RESOURCES) {
            // The prelude is resolved like any other module (issue #177): its own declarations are
            // collected first, then everything is resolved against them, so a signature may name a
            // data the module declares. What it declares must be runtime-backed (see
            // RUNTIME_BACKED_DATA), and the names anchor to the runtime namespace where the
            // implementation classes live.
            Ast.Module parsed = CstFrontend.parse(read(resource));
            Symbols symbols = symbolsOf(parsed, resource);
            Ast.Module module = Resolve.module(parsed, symbols);
            String alias = MODULE_TO_ALIAS.get(module.name());
            if (alias == null) {
                throw new IllegalStateException("prelude resource " + resource
                        + " declares unknown module " + module.name());
            }
            for (Ast.Def def : module.defs()) {
                if (RUNTIME_DEFS.containsKey(def.name())) {
                    throw new IllegalStateException(
                            "the standard library declares `" + def.name() + "` twice");
                }
                RUNTIME_DEFS.put(def.name(), def);
            }
            for (Ast.FnDef fn : module.fns()) {
                String qualified = alias + "." + fn.name();
                // One qualified name, one declaration. The library has no overloading: a name that
                // reads two ways would have to be chosen between, and nothing at a value position
                // could do the choosing. Put into a map, a second one would replace the first in
                // silence, so it is refused where it is loaded.
                if (ENTRIES.containsKey(qualified)) {
                    throw new IllegalStateException(
                            "the standard library declares `" + qualified + "` twice");
                }
                Signature signature = signatureOf(fn, qualified, symbols);
                ENTRIES.put(qualified, new PreludeEntry(fn, signature));
                if (fn.body() instanceof Ast.FnBody.Intrinsic intrinsic) {
                    KERNELS.put(intrinsic.key(), signature);
                }
                BARE_TO_QUALIFIED.putIfAbsent(fn.name(), qualified);
            }
        }
        // Explicit bare→qualified hints. Two kinds need one: the checker built-ins, which have no
        // prelude source to derive from, and every name more than one module defines — the derived
        // hint takes whichever module RESOURCES loads first (bool, string, map, list, set, …), which
        // is an accident of that order rather than the answer a reader wants.
        BARE_TO_QUALIFIED.put("length", "List.length` or `String.length");
        BARE_TO_QUALIFIED.put("toInt", "String.toInt` or `Decimal.toInt");
        BARE_TO_QUALIFIED.put("toDecimal", "String.toDecimal");
        BARE_TO_QUALIFIED.put("fromInt", "String.fromInt` or `Decimal.fromInt");
        BARE_TO_QUALIFIED.put("fromDecimal", "String.fromDecimal");
        BARE_TO_QUALIFIED.put("round", "Decimal.round");
        BARE_TO_QUALIFIED.put("get", "List.get` or `Map.get");
        BARE_TO_QUALIFIED.put("map", "List.map`, `Map.map`, `Set.map`, or `Option.map");
        BARE_TO_QUALIFIED.put("filter", "List.filter`, `Map.filter`, or `Set.filter");
        BARE_TO_QUALIFIED.put("partition", "List.partition` or `Set.partition");
        BARE_TO_QUALIFIED.put("empty", "Map.empty` or `Set.empty");
        BARE_TO_QUALIFIED.put("fold", "List.fold`, `Map.fold`, or `Set.fold");
        BARE_TO_QUALIFIED.put("isEmpty", "List.isEmpty`, `String.isEmpty`, `Map.isEmpty`, or `Set.isEmpty");
        BARE_TO_QUALIFIED.put("size", "Map.size` or `Set.size");
        BARE_TO_QUALIFIED.put("contains", "String.contains` or `Set.contains");
        BARE_TO_QUALIFIED.put("reverse", "List.reverse` or `String.reverse");
        BARE_TO_QUALIFIED.put("concat", "List.concat` or `String.concat");
        BARE_TO_QUALIFIED.put("toList", "Map.toList` or `Set.toList");
        BARE_TO_QUALIFIED.put("fromList", "Map.fromList` or `Set.fromList");
        BARE_TO_QUALIFIED.put("singleton", "Map.singleton` or `Set.singleton");
        BARE_TO_QUALIFIED.put("union", "Map.union` or `Set.union");
        BARE_TO_QUALIFIED.put("intersect", "Map.intersect` or `Set.intersect");
        BARE_TO_QUALIFIED.put("difference", "Map.difference` or `Set.difference");
        BARE_TO_QUALIFIED.put("max", "List.max`, `Int.max`, or `Decimal.max");
        BARE_TO_QUALIFIED.put("min", "List.min`, `Int.min`, or `Decimal.min");
        BARE_TO_QUALIFIED.put("abs", "Int.abs` or `Decimal.abs");
        BARE_TO_QUALIFIED.put("clamp", "Int.clamp` or `Decimal.clamp");
        BARE_TO_QUALIFIED.put("find", "List.find");
        BARE_TO_QUALIFIED.put("sortBy", "List.sortBy");
        BARE_TO_QUALIFIED.put("compare", "Int.compare` or `Decimal.compare");
        BARE_TO_QUALIFIED.put("remainder", "Int.remainder");
        BARE_TO_QUALIFIED.put("add", "Int.add` or `Decimal.add");
        BARE_TO_QUALIFIED.put("subtract", "Int.subtract` or `Decimal.subtract");
        BARE_TO_QUALIFIED.put("multiply", "Int.multiply` or `Decimal.multiply");
        BARE_TO_QUALIFIED.put("divide", "Int.divide` or `Decimal.divide");
    }

    /**
     * What names mean while a prelude source is resolved: its own declarations, anchored to the
     * runtime namespace. Anchoring happens here and nowhere else — every reader below (the scope
     * fallback, the definition lookup) reads what this wrote. A prelude data outside
     * {@link #RUNTIME_BACKED_DATA} is refused: its cases would have no implementation classes.
     * A case of a registered sum is registered with it.
     */
    private static Symbols symbolsOf(Ast.Module m, String resource) {
        Map<String, Ast.Def> declared = TypeChecker.ownDefs(m);
        if (declared.isEmpty()) {
            return Symbols.none();   // signatures over primitives and type variables only
        }
        Set<String> covered = new LinkedHashSet<>();
        for (Ast.Def def : declared.values()) {
            if (def instanceof Ast.SumData sum && RUNTIME_BACKED_DATA.contains(sum.name())) {
                covered.add(sum.name());
                for (Ast.Name c : sum.cases()) {
                    covered.add(c.written());
                }
            }
        }
        Map<String, TypeName> scope = new HashMap<>();
        for (String name : declared.keySet()) {
            if (!covered.contains(name)) {
                throw new IllegalStateException("prelude resource " + resource + " declares `"
                        + name + "`, which is not registered as runtime-backed data");
            }
            scope.put(name, TypeName.runtime(name));
        }
        return Symbols.of(TypeName.RUNTIME,
                Registry.of(Map.of(TypeName.RUNTIME, m)), scope, Map.of());
    }

    /** The runtime-backed declaration {@code name} denotes, or null when there is none. */
    public static Ast.Def runtimeBackedDef(TypeName name) {
        return TypeName.RUNTIME.equals(name.module()) ? RUNTIME_DEFS.get(name.name()) : null;
    }

    /** The runtime-namespace name a bare {@code written} denotes, or null when it denotes none.
     *  The lowest rung of a module's scope: its own declarations and its imports come first. */
    public static TypeName runtimeBackedType(String written) {
        return RUNTIME_DEFS.containsKey(written) ? TypeName.runtime(written) : null;
    }

    /** Every runtime-backed declaration, keyed by bare name — what the runtime namespace declares. */
    public static Map<String, Ast.Def> runtimeBackedDefs() {
        return Collections.unmodifiableMap(RUNTIME_DEFS);
    }

    /** The declared signature of the kernel behind {@code intrinsic "key"}, or null where no core
     *  declaration writes that key. */
    public static Signature kernelSignature(String key) {
        return KERNELS.get(key);
    }

    /** The resolved signature of {@code fn}. A zero-parameter declaration is a value whose type
     *  only the signature can answer — {@code libraryValue} reads it with no call whose arguments
     *  could pin it — and a kernel's calls are checked against the declared result with no body to
     *  infer one from. Either would be an entry answering a type question with nothing, so a
     *  declaration of either kind that writes no return type is refused here. */
    static Signature signatureOf(Ast.FnDef fn, String qualified, Symbols symbols) {
        List<Type> params = new ArrayList<>();
        for (Ast.FnParam p : fn.params()) {
            params.add(TypeOps.resolveParamType(p.type(), symbols));
        }
        Type result = fn.declaredReturn() == null
                ? null : TypeOps.successType(fn.declaredReturn(), symbols);
        if (result == null
                && (fn.params().isEmpty() || fn.body() instanceof Ast.FnBody.Intrinsic)) {
            throw new IllegalStateException("a prelude "
                    + (fn.params().isEmpty() ? "value" : "kernel")
                    + " must declare its return type: `" + qualified + "`");
        }
        return new Signature(params, result);
    }

    private static String read(String resource) {
        try (InputStream in = Prelude.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("missing bundled prelude resource " + resource);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException("failed to read prelude resource " + resource, e);
        }
    }
}
