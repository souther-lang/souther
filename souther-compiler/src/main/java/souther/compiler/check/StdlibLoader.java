package souther.compiler.check;

import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.stdlib.LibraryNames;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Denotation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Reads the standard library the compiler ships in the reserved {@code souther} namespace (ADR-0028,
 * spec §reserved-namespace) into a {@link Stdlib}.
 *
 * <p>The library's modules are packaged as resources. Reading one means resolving and typing it,
 * which is what {@link Resolve}, {@link TypeChecker} and {@link TypeOps} do — so the loader lives
 * beside them, and what it produces does not. A reader that wants to know what the library declares
 * holds a {@link Stdlib}; this is what somebody had to run to obtain one.
 *
 * <p>Every call builds a whole library and hands it over finished. Nothing is memoized here: whether
 * a process keeps one is that process's question, and answering it in the same place as the reading
 * is what made the library a thing that could be observed half built.
 *
 * <h2>All of it is declared before any of it is resolved</h2>
 *
 * <p>The four phases below are the point. Every module is parsed, then every declaration the whole
 * library makes is collected, and only then is anything resolved — against all of them. So a
 * signature in the first module may name a data declared in the last, and the order
 * {@link Reserved#MODULES} lists is the order names are <em>offered</em> in and never decides which
 * names exist.
 *
 * <p>It used to resolve each module against its own declarations as it went, so what a name meant
 * depended on how far the loading had got. That worked only because one module declared data and
 * only that module named it; a second declaration, or a reference from a module listed earlier,
 * resolved to nothing and said so nowhere.
 */
public final class StdlibLoader {

    private StdlibLoader() {
    }

    /** One library module as it was read: what the language calls it, and what it parsed to. */
    private record Parsed(Reserved.StdlibModule declared, Ast.Module module, String resource,
                          DeclaredNames.Index<Ast.Def> indexed) {
    }

    /**
     * The standard library, read from the resources this compiler ships.
     *
     * @throws IllegalStateException where a resource is missing, declares a module it was not listed
     *     under, or carries a declaration the indexing refuses. The library is this compiler's own
     *     source: a fault in it is nobody's mistake to be told about, and is refused where it is read
     *     like the rest of what is checked here.
     */
    public static Stdlib load() {
        List<Parsed> sources = parseEverything();
        Map<String, Ast.Def> declares = everythingTheLibraryDeclares(sources);
        Stdlib.Builder building = Stdlib.builder();
        List<Hir.Module> resolved = new ArrayList<>();
        for (Parsed source : sources) {
            Hir.Module module = Resolve.module(source.module(), symbolsFor(source, declares));
            if (!source.declared().moduleName().equals(module.name())) {
                throw new IllegalStateException("prelude resource " + source.resource()
                        + " declares module " + module.name() + ", not "
                        + source.declared().moduleName());
            }
            resolved.add(module);
            for (Hir.Def def : module.defs()) {
                building.languageDeclares(def);
            }
        }
        for (int i = 0; i < resolved.size(); i++) {
            String alias = sources.get(i).declared().qualifier();
            for (Hir.FnDef fn : resolved.get(i).fns()) {
                ValueName.Stdlib.Operation operation =
                        ValueName.Stdlib.operation(alias, fn.name());
                building.declares(operation,
                        new Stdlib.Entry(fn, signatureOf(fn, operation.qualified())),
                        fn.isPrivate());
            }
        }
        return building.freeze();
    }

    /** Phase one: every module read and parsed, in the order the language lists them.
     *
     * <p>The library ships with the compiler and is in no source of any compile that calls it, so
     * its positions say they stand in for code written there from the moment they are made. A reader
     * reaches the module by the name it imports it under. */
    private static List<Parsed> parseEverything() {
        List<Parsed> parsed = new ArrayList<>();
        for (Reserved.StdlibModule declared : Reserved.MODULES) {
            String resource = "/" + declared.moduleName().replace('.', '/') + ".sou";
            Ast.Module module = CstFrontend.parseWhatAModulePublished(read(resource),
                    new SourceProvenance.TheStandardLibrary(declared.moduleName()));
            parsed.add(new Parsed(declared, module, resource, indexed(module, resource)));
        }
        return parsed;
    }

    /**
     * Phase two: everything the library declares, from every one of its modules, before any of them
     * is resolved.
     *
     * @throws IllegalStateException where a resource carries a declaration the indexing refuses, or
     *     where two of them declare one name — which nothing downstream would report, because
     *     everything downstream reads what this collected
     */
    private static Map<String, Ast.Def> everythingTheLibraryDeclares(List<Parsed> sources) {
        Map<String, Ast.Def> declared = new LinkedHashMap<>();
        Map<String, String> declaredBy = new HashMap<>();
        for (Parsed source : sources) {
            for (Ast.Def def : source.indexed().declarations().values()) {
                String already = declaredBy.put(def.name(), source.resource());
                if (already != null) {
                    throw new IllegalStateException("the standard library declares `" + def.name()
                            + "` in both " + already + " and " + source.resource());
                }
                declared.put(def.name(), def);
            }
        }
        return declared;
    }

    /**
     * Phase three: what one library module is resolved against.
     *
     * <p>Two halves, and they are not the same set. What a name written here <em>means</em> is
     * everything the library declares, so a signature in the first module may name a data declared
     * in the last; what this module <em>declares</em> is its own, which is what the registry holds
     * and what {@code Resolve} reads back as the module's declarations. Given the whole library to
     * both, every module would come back declaring what its neighbours declare.
     *
     * <p>Each declaration is the declaration of the library module that writes it, and says so:
     * {@code souther.decimal} declares {@code RoundingMode}, so that is its identity. What a source
     * writes it as is a separate question and a separate answer ({@link LibraryNames#identityOf}),
     * because the module that declares one is not a qualifier anybody names it by.
     */
    private static SyntaxSymbols symbolsFor(Parsed source, Map<String, Ast.Def> declares) {
        Map<String, Denotation> scope = new HashMap<>();
        Map<String, TypeSymbol> identities = new HashMap<>();
        for (Ast.Def def : declares.values()) {
            TypeSymbol declared = TypeSymbols.declared(def.declaredKey());
            scope.put(def.name(), new Denotation.Denotes(declared));
            identities.put(def.name(), declared);
        }
        String module = source.declared().moduleName();
        return SyntaxSymbols.overTheseLibraryNames(module,
                Registry.ofRead(Map.of(module, new Registry.Declared<>(
                        source.indexed().declarations(),
                        Registry.baseNames(source.module().exposing())))),
                Denoting.of(scope, Map.of()),
                LibraryNames.ofTheLibraryBeingLoaded(identities));
    }

    /** What one library resource declares, as it was written.
     *
     * @throws IllegalStateException where the indexing refuses a declaration. The standard library is
     *     this compiler's own source: a declaration it may not have is a resource shipped in the jar
     *     being wrong, which is refused where it is read like the rest of what is checked here. */
    private static DeclaredNames.Index<Ast.Def> indexed(Ast.Module module, String resource) {
        DeclaredNames.Index<Ast.Def> indexed = Registry.indexed(module);
        if (!indexed.refusals().isEmpty()) {
            throw new IllegalStateException("prelude resource " + resource
                    + " carries a declaration the indexing refused: `"
                    + indexed.refusals().get(0).refused().name() + "`");
        }
        return indexed;
    }

    /** The resolved signature of {@code fn}. A zero-parameter declaration is a value whose type
     *  only the signature can answer — a library value is read with no call whose arguments could
     *  pin it — so one that writes no return type would be an entry answering a type question with
     *  nothing, and is refused here. What a kernel must declare is
     *  {@link souther.compiler.core.KernelSignature}'s to say, and is said where one is made. */
    static Stdlib.Signature signatureOf(Hir.FnDef fn, String qualified) {
        List<Type> params = new ArrayList<>();
        for (Hir.FnParam p : fn.params()) {
            params.add(TypeOps.resolveParamType(p.type()));
        }
        Type result = fn.declaredReturn() == null
                ? null : TypeOps.successType(fn.declaredReturn());
        if (result == null && fn.params().isEmpty()) {
            throw new IllegalStateException(
                    "a prelude value must declare its return type: `" + qualified + "`");
        }
        return new Stdlib.Signature(params, result);
    }

    private static String read(String resource) {
        try (InputStream in = StdlibLoader.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException("missing bundled prelude resource " + resource);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException("failed to read prelude resource " + resource, e);
        }
    }
}
