package souther.compiler.check;

import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.diag.SourceProvenance;
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
 * {@linkplain Hir.FnBody body}, not a second registry.
 *
 * <p>The library publishes no bare names (spec §stdlib), so entries are keyed by the qualified name
 * — {@code List.map}, {@code String.trim}. A module that imports a name writes it without the
 * qualifier; what it reaches is this same entry, since an import elides the qualifier where the call
 * is written and settles nothing else.
 *
 * <p>This is part of the check, not a layer under it. Loading an entry resolves and types the
 * declaration through {@link Resolve}, {@link TypeChecker} and {@link TypeOps}, and the check reads
 * entries back whenever a call names a library operation. The two are one component and are one
 * package for that reason — the dependency between them runs both ways and there is no ordering of
 * them that makes it run one way.
 */
public final class Prelude {

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
    public record PreludeEntry(Hir.FnDef declaration, Signature signature) {
    }

    /** Every declaration the library ships, keyed by qualified name ({@code "List.map"}) — the
     *  {@linkplain #isPrivateMember(String) private} ones included, because the checker and the
     *  backend still have to type and emit what they are behind. */
    private static final Map<String, PreludeEntry> ENTRIES = new LinkedHashMap<>();

    /** The qualified names of the declarations written {@code private}: implementation helpers the
     *  library reaches and no caller can name. Kept apart from {@link #ENTRIES} so that "does this
     *  name exist" and "may this name be written" are two questions with two answers. */
    private static final Set<String> PRIVATE = new LinkedHashSet<>();

    /**
     * Every library name as what a name reaching it denotes, keyed by the qualified spelling.
     *
     * <p>Written where the qualified spelling is made, out of the two values it is made of. A caller
     * holding a qualified name asks here rather than splitting it: the alias and the operation are
     * what the library knew when it loaded, and a name that has been joined and split again is a name
     * that agrees with the original only as long as nobody writes one with a dot in it.
     */
    private static final Map<String, ValueName.Stdlib> OPERATIONS = new LinkedHashMap<>();

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
    private static final Map<String, Hir.Def> RUNTIME_DEFS = new LinkedHashMap<>();

    /** Each kernel's declared signature, keyed by its intrinsic key ({@code "decimal.toInt"}) —
     *  the projection of {@link #ENTRIES} the backend reads to derive a kernel's JVM descriptor
     *  from the declaration rather than repeating it. */
    private static final Map<String, Signature> KERNELS = new LinkedHashMap<>();

    /** The Souther-bodied declarations, as the inliner's table wants them: a materialized projection
     *  of {@link #ENTRIES}, derived once after loading and never written again. */
    private static final Map<String, Hir.FnDef> HELPERS;

    static {
        load();
        Map<String, Hir.FnDef> helpers = new LinkedHashMap<>();
        for (Map.Entry<String, PreludeEntry> e : ENTRIES.entrySet()) {
            if (e.getValue().declaration().body() instanceof Hir.FnBody.Written) {
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

    /** What a sugared name is sugar for: the call it becomes, and the arguments the rewrite supplies
     *  after the ones that were written. {@code List.fold(step, seed, xs)} is
     *  {@code List.foldFrom(step, seed, xs, 0)} — three written, and the index the walk starts at
     *  supplied. Said here whole because two readers need different halves of it: the rewrite
     *  performs it, and anything stated of an operation is stated of the sugar by the arguments that
     *  stand where they stood. A sugar supplies constants and nothing else, which is why they are
     *  numbers here; one that had to supply anything else could not be written down as this and
     *  would say so. */
    public record Rewrite(ValueName.Stdlib target, List<Integer> supplied) {
        public Rewrite {
            supplied = List.copyOf(supplied);
        }

        /** How many of the arguments the sugar is written with stand where they stood — the target's
         *  own count, less what the rewrite adds. */
        public int keptArgs() {
            PreludeEntry entry = ENTRIES.get(target.qualified());
            return entry == null ? 0 : entry.signature().params().size() - supplied.size();
        }
    }

    /** Names that are sugar for another standard-library call, recognised as library functions but
     *  rewritten before inlining. Written as the two values a library name is made of, so that the
     *  sugar and what it becomes are named here the way every other library name is. */
    private static final ValueName.Stdlib FOLD = new ValueName.Stdlib("List", "fold");

    private static final Map<String, Rewrite> SUGARED = Map.of(FOLD.qualified(),
            new Rewrite(new ValueName.Stdlib("List", "foldFrom"), List.of(0)));

    /** A sugar has no declaration, so nothing above put it among the operations; it is a name a
     * reader may write, so it belongs there. Placed after {@link #SUGARED} because a static
     * initializer reads what the ones above it have already written. */
    static {
        OPERATIONS.put(FOLD.qualified(), FOLD);
    }

    /** Bare name → every published name it could be, in {@link Reserved#MODULES} order:
     *  {@code insert} is {@code Map.insert} or {@code Set.insert}. Derived from the published
     *  surface — which includes the sugar, so it is built after {@link #SUGARED} — so a function
     *  added to a module is offered by every reader of this the day it is added. */
    private static final Map<String, List<String>> CANDIDATES = candidates();

    private static Map<String, List<String>> candidates() {
        Map<String, List<String>> byBareName = new LinkedHashMap<>();
        for (String qualified : published()) {
            byBareName.computeIfAbsent(qualified.substring(qualified.indexOf('.') + 1),
                    bare -> new ArrayList<>()).add(qualified);
        }
        byBareName.replaceAll((bare, qualified) -> List.copyOf(qualified));
        return Collections.unmodifiableMap(byBareName);
    }

    /** Whether {@code qualifiedName} is one of those — a name no tree holds after the rewrite. */
    public static boolean sugared(String qualifiedName) {
        return SUGARED.containsKey(qualifiedName);
    }

    /** What {@code qualifiedName} rewrites to, or null where it is not sugar. */
    public static Rewrite rewriteOf(String qualifiedName) {
        return SUGARED.get(qualifiedName);
    }

    /** Every sugared name, by what it rewrites to. */
    public static Map<String, Rewrite> rewrites() {
        return SUGARED;
    }

    /** Whether {@code qualifiedName} (e.g. {@code "List.map"}) is a standard-library function — a
     *  declared one, or a sugar for one. Sugar has no declaration of its own, so this is wider than
     *  {@link #entry(String)} answering: {@code List.fold} is a library function and has no entry. */
    public static boolean isLibraryFunction(String qualifiedName) {
        return ENTRIES.containsKey(qualifiedName) || SUGARED.containsKey(qualifiedName);
    }

    /** The library's entry for {@code qualifiedName}, or null where the library declares no such
     *  name — including for {@linkplain #sugared(String) sugar}, which is a rewrite, not a
     *  declaration. */
    public static PreludeEntry entry(String qualifiedName) {
        return ENTRIES.get(qualifiedName);
    }

    /** Whether {@code qualifiedName} is a library <em>value</em> standing for an empty collection —
     *  {@code Map.empty}, {@code Set.empty}. Written with no parameter list, so it has no argument to
     *  learn its element type from and takes it from the position it is written in, as {@code []}
     *  does. Asked rather than spelled out: which names those are is the library's own to say. */
    public static boolean isEmptyCollectionValue(String qualifiedName) {
        PreludeEntry entry = ENTRIES.get(qualifiedName);
        return entry != null && entry.declaration().params().isEmpty();
    }

    /** Every entry, keyed by qualified name, in declaration order — private ones included. */
    public static Map<String, PreludeEntry> entries() {
        return Collections.unmodifiableMap(ENTRIES);
    }

    /**
     * What a name reaching {@code qualifiedName} denotes, or null where the library has no such name.
     *
     * <p>The alias and the operation as the library wrote them, so a caller holding a qualified
     * spelling gets them back rather than splitting it. The library is the only thing that knows
     * which part is which: {@code souther.list} declares {@code foldFrom} and publishes it under
     * {@code List}, and the spelling says nothing about either.
     */
    public static ValueName.Stdlib operation(String qualifiedName) {
        return OPERATIONS.get(qualifiedName);
    }

    /** Whether {@code qualifiedName} names a declaration the library keeps to itself. Such a name
     *  may be written inside the reserved namespace and nowhere else, so everything outside it is
     *  told the library has no such member. */
    public static boolean isPrivateMember(String qualifiedName) {
        return PRIVATE.contains(qualifiedName);
    }

    /** The library's published surface: every qualified name a module outside the reserved
     *  namespace may write, in declaration order. A sugar has no declaration to be ordered by, so it
     *  is placed at the end of the module it belongs to — a reader of this list is reading one
     *  module's vocabulary at a time, and a name that reads as {@code List}'s belongs among them. */
    public static Set<String> published() {
        Set<String> names = new LinkedHashSet<>();
        for (String qualified : ENTRIES.keySet()) {
            if (PRIVATE.contains(qualified)) {
                continue;
            }
            names.add(qualified);
        }
        names.addAll(SUGARED.keySet());
        Set<String> byModule = new LinkedHashSet<>();
        for (String qualifier : QUALIFIERS) {
            for (String name : names) {
                if (OPERATIONS.get(name).alias().equals(qualifier)) {
                    byModule.add(name);
                }
            }
        }
        byModule.addAll(names);   // anything under a qualifier not in the load order
        return Collections.unmodifiableSet(byModule);
    }

    /** The Souther-bodied declarations (inlined at call sites), keyed by qualified name, in
     *  declaration order. */
    public static Map<String, Hir.FnDef> helpers() {
        return HELPERS;
    }

    /**
     * Every published name a bare {@code bareName} could be reaching for, in {@link Reserved#MODULES}
     * order — {@code ["Map.insert", "Set.insert"]} — or empty where the library publishes no such
     * name. What a report does with more than one is offer them all: a reader told only about
     * {@code Map.insert} has been told the library has no {@code Set.insert}.
     */
    public static List<String> qualifiedCandidates(String bareName) {
        return CANDIDATES.getOrDefault(bareName, List.of());
    }

    /** Those candidates as a diagnostic writes them: {@code `Map.insert`, `Set.insert`}. The
     *  sentence they sit in belongs to the message catalog, so what is built here is the list and
     *  not a phrase — an "or" assembled in Java would be an English word in the Japanese report. */
    public static String candidateList(String bareName) {
        StringBuilder sb = new StringBuilder();
        for (String qualified : qualifiedCandidates(bareName)) {
            if (!sb.isEmpty()) {
                sb.append(", ");
            }
            sb.append('`').append(qualified).append('`');
        }
        return sb.toString();
    }

    private static void load() {
        for (Reserved.StdlibModule declared : Reserved.MODULES) {
            String resource = "/" + declared.moduleName().replace('.', '/') + ".sou";
            // The prelude is resolved like any other module (issue #177): its own declarations are
            // collected first, then everything is resolved against them, so a signature may name a
            // data the module declares. What it declares must be runtime-backed (see
            // RUNTIME_BACKED_DATA), and the names anchor to the runtime namespace where the
            // implementation classes live.
            // The library ships with the compiler and is in no source of any compile that calls it,
            // so its positions say they stand in for code written there from the moment they are
            // made. A reader reaches the module by the name it imports it under.
            Ast.Module parsed = CstFrontend.parseWhatAModulePublished(read(resource),
                    new SourceProvenance.TheStandardLibrary(declared.moduleName()));
            Hir.Module module = Resolve.module(parsed, symbolsOf(parsed, resource));
            if (!declared.moduleName().equals(module.name())) {
                throw new IllegalStateException("prelude resource " + resource + " declares module "
                        + module.name() + ", not " + declared.moduleName());
            }
            String alias = declared.qualifier();
            for (Hir.Def def : module.defs()) {
                if (RUNTIME_DEFS.containsKey(def.name())) {
                    throw new IllegalStateException(
                            "the standard library declares `" + def.name() + "` twice");
                }
                RUNTIME_DEFS.put(def.name(), def);
            }
            for (Hir.FnDef fn : module.fns()) {
                ValueName.Stdlib operation = new ValueName.Stdlib(alias, fn.name());
                String qualified = operation.qualified();
                // One qualified name, one declaration. The library has no overloading: a name that
                // reads two ways would have to be chosen between, and nothing at a value position
                // could do the choosing. Put into a map, a second one would replace the first in
                // silence, so it is refused where it is loaded.
                if (ENTRIES.containsKey(qualified)) {
                    throw new IllegalStateException(
                            "the standard library declares `" + qualified + "` twice");
                }
                Signature signature = signatureOf(fn, qualified);
                ENTRIES.put(qualified, new PreludeEntry(fn, signature));
                OPERATIONS.put(qualified, operation);
                if (fn.body() instanceof Hir.FnBody.Intrinsic intrinsic) {
                    KERNELS.put(intrinsic.key(), signature);
                }
                if (fn.isPrivate()) {
                    PRIVATE.add(qualified);
                }
            }
        }
    }

    /**
     * What names mean while a prelude source is resolved: its own declarations, anchored to the
     * runtime namespace. Anchoring happens here and nowhere else — every reader below (the scope
     * fallback, the definition lookup) reads what this wrote. A prelude data outside
     * {@link #RUNTIME_BACKED_DATA} is refused: its cases would have no implementation classes.
     * A case of a registered sum is registered with it.
     */
    private static SyntaxSymbols symbolsOf(Ast.Module m, String resource) {
        DeclaredNames.Index<Ast.Def> indexed = Registry.indexed(m);
        if (!indexed.refusals().isEmpty()) {
            // The standard library is this compiler's own source. A declaration it may not have is
            // nobody's mistake to be told about: it is a resource shipped in the jar being wrong,
            // which is refused where it is loaded like the rest of what is checked here.
            throw new IllegalStateException("prelude resource " + resource + " carries a"
                    + " declaration the indexing refused: `"
                    + indexed.refusals().get(0).refused().name() + "`");
        }
        Map<String, Ast.Def> declared = indexed.declarations();
        if (declared.isEmpty()) {
            return SyntaxSymbols.none();   // signatures over primitives and type variables only
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
        Map<String, Denotation> scope = new HashMap<>();
        for (String name : declared.keySet()) {
            if (!covered.contains(name)) {
                throw new IllegalStateException("prelude resource " + resource + " declares `"
                        + name + "`, which is not registered as runtime-backed data");
            }
            scope.put(name, new Denotation.Denotes(TypeSymbol.runtime(name)));
        }
        return SyntaxSymbols.of(TypeSymbol.RUNTIME,
                Registry.ofRead(Map.of(TypeSymbol.RUNTIME, new Registry.Declared<>(
                        declared, Registry.baseNames(m.exposing())))),
                Denoting.of(scope, Map.of()));
    }

    /** The runtime-backed declaration {@code name} denotes, or null when there is none. */
    public static Hir.Def runtimeBackedDef(TypeKey address) {
        return TypeSymbol.RUNTIME.equals(address.module()) ? RUNTIME_DEFS.get(address.name()) : null;
    }

    /** The runtime-namespace name a bare {@code written} denotes, or null when it denotes none.
     *  The lowest rung of a module's scope: its own declarations and its imports come first. */
    public static TypeSymbol runtimeBackedType(String written) {
        return RUNTIME_DEFS.containsKey(written) ? TypeSymbol.runtime(written) : null;
    }

    /** Every runtime-backed declaration, keyed by bare name — what the runtime namespace declares. */
    public static Map<String, Hir.Def> runtimeBackedDefs() {
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
    static Signature signatureOf(Hir.FnDef fn, String qualified) {
        List<Type> params = new ArrayList<>();
        for (Hir.FnParam p : fn.params()) {
            params.add(TypeOps.resolveParamType(p.type()));
        }
        Type result = fn.declaredReturn() == null
                ? null : TypeOps.successType(fn.declaredReturn());
        if (result == null
                && (fn.params().isEmpty() || fn.body() instanceof Hir.FnBody.Intrinsic)) {
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
