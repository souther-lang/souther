package souther.compiler.query;

import souther.compiler.MemoryClassLoader;
import souther.compiler.ast.Ast;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.DataChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.meta.ModulePath;

import souther.compiler.types.TypeName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The bytecode a module comes to, and the two things that can only be asked once it exists: whether
 * its constant constructions satisfy their invariants, and whether its examples hold.
 *
 * <p>Both of those load classes, so both read {@link Linked} rather than one module's own — an
 * example may reach across an import, and the class it reaches has to be there. {@link All} is what
 * a build writes out, and nothing that runs code reads it: a key that did would be recomputed by an
 * edit to any module in the workspace.
 */
public final class Output {

    private Output() {}

    /**
     * One module's classes, with its declarations stamped on. The declarations go on before anything
     * loads a class, so what a jar carries is the same bytes this compile checked.
     */
    public record Classes(String name) implements Key<Map<String, byte[]>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, byte[]>> compute(Db db) {
            Answer<TypeChecker.Checked> checked = db.ask(new Bodies.Checked(name));
            Answer<Lower.Lowered> lowering = db.ask(new Bodies.Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> imported = db.ask(new Bodies.Imported(name));
            Answer<Set<String>> injected = db.ask(new Bodies.ImportedInjected(name));
            Answer<Map<String, ReqSig>> callees = db.ask(new Bodies.CalleeSigs(name));
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Map<String, List<BehaviorRequirement>>> requirements =
                    db.ask(new Bodies.Requirements(name));
            // A derived decoder maps a clause onto the Raoh constraint that says the same thing, and it
            // is written against the operations an author wrote — which the lowered module no longer has.
            Answer<Map<TypeName, List<Ast.InvariantClause>>> dischargeClauses =
                    db.ask(new Shapes.InvariantsForDischarge(name));
            if (!checked.present() || !lowering.present() || !scope.present() || !imported.present()
                    || !injected.present() || !callees.present() || !prepared.present()
                    || !requirements.present() || !dischargeClauses.present()) {
                return Answer.absent();
            }
            try {
                Map<String, byte[]> classes = new LinkedHashMap<>(Backend.generate(
                        lowering.value().lowered(), scope.value(), typePackages(prepared.value()),
                        imported.value(), injected.value(), callees.value(), requirements.value(),
                        checked.value(), dischargeClauses.value()));
                stamp(db, classes);
                return Answer.of(Ordered.map(classes));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }

        /**
         * Puts this module's declarations on its classes, as its source wrote them.
         *
         * <p>Nothing here can fail in a way worth reporting. A module with no source of its own was
         * read off the path, and its jar was stamped where it was built; and the declarations are
         * only asked for once the module has checked, so they are there.
         */
        private void stamp(Db db, Map<String, byte[]> classes) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            String id = layout == null ? null : layout.idOfModule().get(name);
            if (id == null) {
                return;
            }
            CstFrontend.Parsed written = db.ask(new Front.Parsed(id)).value();
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            Set<String> injected = db.ask(new Bodies.Injected(name)).value();
            if (written == null || !sigs.present() || injected == null) {
                return;
            }
            ModuleMetadata.stamp(classes, written.module(), written.slices(), sigs.value(), injected);
        }

        /** Maps each imported type name to its declaring module, for cross-package references. */
        private Map<String, String> typePackages(Ast.Module m) {
            Map<String, String> packages = new LinkedHashMap<>();
            for (Ast.Import imp : m.imports()) {
                for (String imported : imp.names()) {
                    packages.put(imported, imp.module());
                }
            }
            return packages;
        }
    }

    /**
     * Every class this compilation generates. A module that did not check contributes none, which is
     * what makes an example of a module that reaches it fail to load rather than run against
     * something that was never checked.
     */
    public record All() implements Key<Map<String, byte[]>> {
        @Override
        public Answer<Map<String, byte[]>> compute(Db db) {
            List<String> declared = db.ask(new Front.Declared()).value();
            Map<String, byte[]> all = new LinkedHashMap<>();
            if (declared == null) {
                return Answer.of(Map.of());
            }
            for (String name : declared) {
                Map<String, byte[]> classes = db.ask(new Classes(name)).value();
                if (classes != null) {
                    all.putAll(classes);
                }
            }
            return Answer.of(Ordered.map(all));
        }
    }

    /**
     * Every module whose classes a module can load: itself, and what it imports, transitively.
     *
     * <p>An example row constructs values of the types its module names and applies behaviors those
     * types reach, and a name it can write is one an import brought in — so the import graph is the
     * bound on what its evaluation loads. A module outside it cannot be reached by any name the row
     * can write.
     *
     * <p>The walk is iterative rather than a question asking itself about the module it reached,
     * because two modules naming each other would then be a question that depends on itself. That is
     * already an error, and it is found before any of this is asked, but this key is asked while the
     * error is on screen too.
     */
    public record Reaches(String name) implements Key<List<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<String>> compute(Db db) {
            Set<String> reached = new LinkedHashSet<>();
            Deque<String> pending = new ArrayDeque<>();
            pending.add(name);
            while (!pending.isEmpty()) {
                String module = pending.removeFirst();
                if (!reached.add(module)) {
                    continue;
                }
                List<String> imports = db.ask(new Front.ImportedModules(module)).value();
                if (imports != null) {
                    pending.addAll(imports);
                }
            }
            return Answer.of(List.copyOf(reached));
        }
    }

    /**
     * The classes an evaluation of one module's code loads: its own, and those of every module it
     * reaches.
     *
     * <p>Not {@link All}. A module's classes are a map of arrays, and arrays compare by identity, so
     * regenerating a module always counts as a change — and a key that read every module's classes
     * would be recomputed by an edit anywhere in the workspace, however far from it. Reading only
     * what it reaches is what keeps an edit to one module from re-running the examples of every
     * other one.
     */
    public record Linked(String name) implements Key<Map<String, byte[]>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, byte[]>> compute(Db db) {
            List<String> reaches = db.ask(new Reaches(name)).value();
            if (reaches == null) {
                return Answer.of(Map.of());
            }
            Map<String, byte[]> linked = new LinkedHashMap<>();
            // Furthest first, so the module being evaluated is put on last: a name two of them
            // generate is the near one's, which is the order All puts them in as well.
            for (int i = reaches.size() - 1; i >= 0; i--) {
                Map<String, byte[]> classes = db.ask(new Classes(reaches.get(i))).value();
                if (classes != null) {
                    linked.putAll(classes);
                }
            }
            return Answer.of(Ordered.map(linked));
        }
    }

    /** The class loader an evaluation runs against: this compilation's classes over the ones the
     * projects it depends on already built. */
    static ClassLoader loader(Db db, Map<String, byte[]> classes) {
        ModulePath path = db.ask(new Front.Path()).value();
        ClassLoader parent = path == null ? Output.class.getClassLoader()
                : path.loader(Output.class.getClassLoader());
        return new MemoryClassLoader(classes, parent);
    }

    /**
     * Whether each constant newtype construction in a module satisfies its invariant, by running the
     * same bytecode a run-time construction would. A check that cannot be loaded or run here is left
     * to the run-time check.
     */
    public record ConstConstructions(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!prepared.present() || !scope.present()) {
                return Answer.absent();
            }
            List<DataChecker.ConstCheck> checks;
            try {
                checks = DataChecker.constNewtypeChecks(prepared.value(), scope.value());
            } catch (CompileException e) {
                return Answer.absent(e);
            }
            if (checks.isEmpty()) {
                return Answer.of(Boolean.TRUE);
            }
            Map<String, byte[]> classes = db.ask(new Linked(name)).value();
            if (classes == null) {
                return Answer.absent();
            }
            ClassLoader loader = loader(db, classes);
            List<Report> reports = new ArrayList<>();
            for (DataChecker.ConstCheck check : checks) {
                boolean holds;
                Class<?> ctfe;
                try {
                    ctfe = Class.forName(
                            check.type().module() + "." + check.type().name() + "$Ctfe", true, loader);
                    holds = (boolean) ctfe.getMethod("check", paramClass(check.value()))
                            .invoke(null, check.value());
                } catch (ReflectiveOperationException | LinkageError _) {
                    continue;   // cannot evaluate at compile time; the run-time check still applies
                }
                if (!holds) {
                    String shown = check.typeName() + "("
                            + (check.value() instanceof String s ? "\"" + s + "\"" : check.value()) + ")";
                    String clause = failingClause(db, check, ctfe);
                    reports.add(Report.raised(
                            Diagnostic.of(null, clause == null
                                            ? "check.const.invariant" : "check.const.invariant.clause")
                                    .title("check.construct.title")
                                    .at(check.pos()).args(shown, clause).build(),
                            "`" + shown + "` violates its invariant"
                                    + (clause == null ? "." : " `" + clause + "`.")));
                }
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
        }

        /**
         * The name of the clause this constant breaks, or null where the clause carries none or the
         * declaration cannot be read here. The same run-time checks the decoder refines with are asked
         * one at a time, in declaration order, so the clause named is the one a construction would
         * report.
         */
        private String failingClause(Db db, DataChecker.ConstCheck check, Class<?> ctfe) {
            Answer<Ast.Module> declaring = db.ask(new Shapes.Prepared(check.type().module()));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(check.type().module()));
            if (!declaring.present() || !scope.present()) {
                return null;
            }
            List<Ast.InvariantClause> clauses = null;
            for (Ast.Def def : declaring.value().defs()) {
                if (def instanceof Ast.Data d && d.name().equals(check.type().name())) {
                    clauses = TypeOps.effectiveInvariants(d, scope.value());
                }
            }
            if (clauses == null) {
                return null;
            }
            for (int i = 0; i < clauses.size(); i++) {
                try {
                    boolean holds = (boolean) ctfe.getMethod(Backend.clauseCheck(i),
                            paramClass(check.value())).invoke(null, check.value());
                    if (!holds) {
                        return clauses.get(i).name().orElse(null);
                    }
                } catch (ReflectiveOperationException | LinkageError _) {
                    return null;
                }
            }
            return null;
        }

        private Class<?> paramClass(Object v) {
            if (v instanceof Long) {
                return long.class;
            }
            if (v instanceof Boolean) {
                return boolean.class;
            }
            return v.getClass();   // String, BigDecimal
        }
    }

    /**
     * The examples of one module, evaluated. Every module's examples are evaluated before any
     * failure stops a compile, so a change to a widely-imported data says how far it reaches in one
     * compile rather than one module per round.
     */
    public record Examples(String name, String sourceId) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public String sourceId() {
            return sourceId;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            if (db.ask(new Bodies.Checked(name)).value() == null) {
                return Answer.absent();   // a module that did not check has nothing to run
            }
            Map<String, byte[]> classes = db.ask(new Linked(name)).value();
            if (classes == null) {
                return Answer.absent();
            }
            Ast.Module rows = written(db, prepared.value());
            if (rows.examples().isEmpty()) {
                return Answer.of(Boolean.TRUE);
            }
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(name)).value();
            if (requirements == null) {
                return Answer.absent();
            }
            List<Report> reports = new ArrayList<>(alreadyDeclared(db));
            if (!reports.isEmpty()) {
                return Answer.absent(reports);   // a row naming one would read the other declaration
            }
            Map<String, Ast.FnDef> values = db.ask(new Bodies.Helpers(name)).value();
            for (Diagnostic failure : souther.compiler.ExampleVerifier.check(rows, scope.value(),
                    sigs.value(), classes, requirements, loader(db, Map.of()),
                    values == null ? Map.of() : values)) {
                reports.add(Report.of(failure));
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
        }

        /**
         * A value this source declares under a name something already declares — the module itself, or an
         * attached file ahead of this one. The rows would read that other declaration, so the one written
         * here would say nothing.
         *
         * <p>Reported from this key rather than from the module's own duplicate check because a position
         * is a line and a column: the module's key can only be quoted against the module's file, and the
         * position is in this one.
         */
        private List<Report> alreadyDeclared(Db db) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            if (layout == null || sourceId == null || sourceId.equals(layout.idOfModule().get(name))) {
                return List.of();   // the module's own source declares what it declares
            }
            Set<String> taken = new LinkedHashSet<>(declaredIn(db, layout.idOfModule().get(name)));
            List<Report> reports = new ArrayList<>();
            for (String id : layout.exampleFilesOf().getOrDefault(name, List.of())) {
                CstFrontend.Parsed parsed = db.ask(new Front.Parsed(id)).value();
                if (parsed == null) {
                    continue;
                }
                for (Ast.FnDef value : parsed.module().fns()) {
                    boolean fresh = taken.add(value.name());
                    if (!fresh && id.equals(sourceId)) {
                        reports.add(Report.of(Diagnostic.of("E1906", "check.example.file.declared")
                                .title("check.example.title").at(value.pos(), value.name().length())
                                .args(value.name(), name).build()));
                    }
                }
                if (id.equals(sourceId)) {
                    break;   // the files after this one are their own key's to report
                }
            }
            return reports;
        }

        /** The names the values of one source declare, or none where nothing parsed it. */
        private Set<String> declaredIn(Db db, String id) {
            Set<String> names = new LinkedHashSet<>();
            CstFrontend.Parsed parsed = id == null ? null : db.ask(new Front.Parsed(id)).value();
            if (parsed != null) {
                for (Ast.FnDef fn : parsed.module().fns()) {
                    names.add(fn.name());
                }
            }
            return names;
        }

        /** The module carrying only the rows written in {@code sourceId}. The fakes stay whole: a
         * module's own fakes are what its attached files' rows run against, and the other way
         * round. */
        private Ast.Module written(Db db, Ast.Module m) {
            List<String> origins = db.ask(new Front.ExampleOrigins(name)).value();
            if (origins == null || origins.size() != m.examples().size()) {
                return m;
            }
            List<Ast.Example> mine = new ArrayList<>();
            for (int i = 0; i < origins.size(); i++) {
                if (origins.get(i).equals(sourceId)) {
                    mine.add(m.examples().get(i));
                }
            }
            return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), m.defs(),
                    m.behaviors(), m.fns(), mine, m.fakes(), m.exampleFileTarget(), m.pos());
        }
    }
}
