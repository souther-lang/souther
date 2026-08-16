package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.CompilationUniverse;
import souther.compiler.query.Db;
import souther.compiler.query.Front;
import souther.compiler.query.Names;
import souther.compiler.types.Denotation;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module means the same thing whichever universe was asked for the modules around it.
 *
 * <p>What a name written in a module can mean was assembled twice — once by a compilation reading
 * its own sources, once by a reader putting published classes back together — and the two agreed
 * only by having been written to agree. They did not, and what it cost was a model that compiled in
 * the project that wrote it and refused to be imported anywhere else. So the assembly is one thing
 * now, and this holds it to that: the same module, resolved against a universe answered by a
 * compilation and against one answered out of a fixed set of readings, comes back as one module.
 *
 * <p>The two universes here fetch differently on purpose — one is asked a name at a time and reads
 * as it goes, the other was read up front — and that is meant to be the whole of the difference
 * between them.
 */
class WhatANameMeansDoesNotDependOnWhichUniverseAnsweredTest {

    /** Publishes a type an import brings in bare, a value a reader writes bare, and a behavior a
     *  reader names through its module. */
    private static final String UP = """
            module scope.up exposing ( In, Mid, twice, standard )
            data In = { n: Int }
            data Mid = { n: Int }
            let standard = 100
            behavior twice : (i: In) -> Mid constructs Mid
            let twice (i) = Mid { n = i.n * 2 }
            """;

    /** Reaches all three, and through an alias — so the scope has to hold what the alias names, what
     *  the line brought in, and an import nobody wrote for the stage. */
    private static final String DOWN = """
            module scope.down exposing ( Out, Tag, flow : Out )
            import String ( length )
            import scope.up as U ( Mid, standard )
            data Out = { n: Int }
            data Tag = String
                invariant length(value) > 0
            behavior plus : (m: Mid) -> Out constructs Out
            let plus (m) = Out { n = m.n + standard }
            behavior flow = U.twice >-> plus
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("up.sou", UP);
        byId.put("down.sou", DOWN);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        // Asked of what was said and not of the map it arrives in: a map with a list per source is
        // never empty, and a check on the map would pass whatever was in the lists.
        assertTrue(compilation.diagnostics().values().stream().allMatch(java.util.List::isEmpty),
                () -> "the model is meant to compile: " + compilation.diagnostics());
        return compilation;
    }

    /** Every module of {@code db}, as that compilation read it — the readings a second universe is
     * built out of. Taken from the compilation so that the two universes differ in how a module is
     * fetched and in nothing else: a module parsed again here would carry another file's positions,
     * and the modules would differ for a reason that is not the one being measured. */
    private static Map<String, ModuleUniverse.InSight> readings(Db db) {
        ModuleUniverse compiling = CompilationUniverse.over(db);
        Map<String, ModuleUniverse.InSight> read = new LinkedHashMap<>();
        for (String name : db.ask(new Front.ModuleNames()).value()) {
            read.put(name, compiling.module(name));
        }
        return read;
    }

    private static ModuleUniverse.InSight.Read read(Map<String, ModuleUniverse.InSight> readings,
                                                    String module) {
        return assertInstanceOf(ModuleUniverse.InSight.Read.class, readings.get(module));
    }

    /** The module a scope is assembled for, as this compilation puts it together. */
    private static Scoping.Subject subject(Db db, String module) {
        Scoping.Subject subject = CompilationUniverse.subject(db, module);
        assertNotNull(subject, module);
        return subject;
    }

    /** What resolution reads other modules by: what each reading of them settled. */
    private static Registry<Ast.Def> declaredBy(Map<String, ModuleUniverse.InSight> readings) {
        Map<String, Map<String, Ast.Def>> declared = new LinkedHashMap<>();
        Map<String, java.util.Set<String>> exposed = new LinkedHashMap<>();
        readings.forEach((name, sighted) -> {
            if (sighted instanceof ModuleUniverse.InSight.Read there) {
                declared.put(name, there.declarations());
                exposed.put(name, Registry.baseNames(there.module().exposing()));
            }
        });
        return Registry.ofRead(declared, exposed);
    }

    /** {@code module} resolved against {@code universe}, by the one assembly there is. */
    private static Hir.Module resolvedAgainst(ModuleUniverse universe, Scoping.Subject subject,
                                              Map<String, ModuleUniverse.InSight> readings) {
        Scoping.Scoped scoped = Scoping.of(universe, subject);
        assertEquals(java.util.List.of(), scoped.refused(),
                "nothing about this model is refused");
        Resolve.Resolution answered = Resolve.resolving(subject.read().module(),
                scoped.writtenSymbols(declaredBy(readings)), scoped.values());
        assertEquals(java.util.List.of(), answered.unresolved(),
                () -> "every name was answered: " + answered.unresolved());
        return answered.module();
    }

    @Test
    void oneModuleResolvedAgainstTwoUniversesIsOneModule() {
        Compilation compilation = compiled();
        Db db = compilation.db();
        Hir.Module byTheCompilation = db.ask(new Names.Resolved("scope.down")).value();

        Map<String, ModuleUniverse.InSight> readings = readings(db);
        Hir.Module byWhatWasRead = resolvedAgainst(new ModuleUniverse.OfWhatIsRead(readings),
                subject(db, "scope.down"), readings);

        assertEquals(byTheCompilation, byWhatWasRead,
                "which universe answered is not something a resolved module can differ by");
    }

    /**
     * A module the universe has and cannot read leaves the names it was to bring in denoting
     * nothing, and says nothing about it.
     *
     * <p>The half of the three answers that is easiest to lose. Whatever is wrong with that module
     * is said where it is, and saying it again here sends an author to a file that is fine — so a
     * universe that answered only "here" or "not here" would report an unknown module for one that
     * is right there.
     */
    @Test
    void aModuleTheUniverseCannotReadIsNotReportedAsMissing() {
        Db db = compiled().db();
        Map<String, ModuleUniverse.InSight> readings = readings(db);
        Scoping.Subject down = subject(db, "scope.down");
        readings.put("scope.up", ModuleUniverse.InSight.UNREADABLE);

        Scoping.Scoped scoped =
                Scoping.of(new ModuleUniverse.OfWhatIsRead(readings), down);

        assertEquals(java.util.List.of(), scoped.refused(),
                "the module is there; what is wrong with it is answered where it is");
        assertEquals(Denotation.STANDS_FOR_NOTHING, scoped.denotations().get("Mid"),
                "a name an import could not bring in is in scope denoting nothing, so a use of it"
                        + " takes the error type rather than reporting an unknown type at each use");
        assertFalse(scoped.reachable().behaviorsWhole(),
                "and the behaviors in scope are not claimed to be all of them: a bare name this"
                        + " module writes may have come from the module that could not be read, so"
                        + " a misspelt one is left unanswered rather than reported here");
    }

    /**
     * A reading whose library names were dropped cannot answer the bare names its own import lines
     * brought in.
     *
     * <p>What {@link ModuleUniverse.InSight.Read} holding both is for, written as the thing that
     * goes wrong without it. The {@code import String ( length )} line is gone from the module by
     * the time anything resolves against it, so the table those lines filled is the only thing that
     * says what {@code length} means here — and a universe free to answer the module without it
     * answers a module that is perfectly good as one whose invariant names nothing.
     */
    @Test
    void aReadingWithoutItsLibraryNamesCannotAnswerWhatItsImportsBroughtIn() {
        Db db = compiled().db();
        Map<String, ModuleUniverse.InSight> readings = readings(db);
        Scoping.Subject withoutTheTable =
                new Scoping.Subject(read(readings, "scope.down"), Map.of());

        Scoping.Scoped scoped =
                Scoping.of(new ModuleUniverse.OfWhatIsRead(readings), withoutTheTable);
        Resolve.Resolution answered = Resolve.resolving(withoutTheTable.read().module(),
                scoped.writtenSymbols(declaredBy(readings)), scoped.values());

        assertTrue(answered.unresolved().stream()
                        .anyMatch(e -> e.getMessage().contains("length")),
                () -> "`length` is answered by the table its import line filled, and by nothing"
                        + " else: " + answered.unresolved());
    }

    /** A module no universe has is the importer's mistake, and is refused on the line that names
     *  it. */
    @Test
    void aModuleNoUniverseHasIsRefusedOnTheImportLine() {
        Db db = compiled().db();
        Map<String, ModuleUniverse.InSight> readings = readings(db);
        Scoping.Subject down = subject(db, "scope.down");
        readings.remove("scope.up");

        Scoping.Scoped scoped =
                Scoping.of(new ModuleUniverse.OfWhatIsRead(readings), down);

        assertEquals(1, scoped.refused().size(), scoped.refused()::toString);
        Scoping.Refusal.NoSuchModule refused = assertInstanceOf(
                Scoping.Refusal.NoSuchModule.class, scoped.refused().get(0));
        assertEquals("scope.up", refused.imp().module());
    }
}
