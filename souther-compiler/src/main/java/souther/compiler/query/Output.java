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
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.meta.ModulePath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The bytecode a module comes to, and the two things that can only be asked once it exists: whether
 * its constant constructions satisfy their invariants, and whether its examples hold.
 *
 * <p>Both of those load classes, so both read {@link All} rather than one module's own — an example
 * may reach across an import, and the class it reaches has to be there.
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
            if (!checked.present() || !lowering.present() || !scope.present() || !imported.present()
                    || !injected.present() || !callees.present() || !prepared.present()
                    || !requirements.present()) {
                return Answer.absent();
            }
            try {
                Map<String, byte[]> classes = new LinkedHashMap<>(Backend.generate(
                        lowering.value().lowered(), scope.value(), typePackages(prepared.value()),
                        imported.value(), injected.value(), callees.value(), requirements.value(),
                        checked.value()));
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
            Map<String, byte[]> classes = db.ask(new All()).value();
            if (classes == null) {
                return Answer.absent();
            }
            ClassLoader loader = loader(db, classes);
            List<Report> reports = new ArrayList<>();
            for (DataChecker.ConstCheck check : checks) {
                boolean holds;
                try {
                    Class<?> ctfe = Class.forName(
                            check.type().module() + "." + check.type().name() + "$Ctfe", true, loader);
                    holds = (boolean) ctfe.getMethod("check", paramClass(check.value()))
                            .invoke(null, check.value());
                } catch (ReflectiveOperationException | LinkageError _) {
                    continue;   // cannot evaluate at compile time; the run-time check still applies
                }
                if (!holds) {
                    String shown = check.typeName() + "("
                            + (check.value() instanceof String s ? "\"" + s + "\"" : check.value()) + ")";
                    reports.add(Report.raised(
                            Diagnostic.of(null, "check.const.invariant").title("check.construct.title")
                                    .at(check.pos()).args(shown).build(),
                            "`" + shown + "` violates its invariant."));
                }
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
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
            Map<String, byte[]> classes = db.ask(new All()).value();
            if (classes == null) {
                return Answer.absent();
            }
            Ast.Module rows = written(db, prepared.value());
            if (rows.examples().isEmpty()) {
                return Answer.of(Boolean.TRUE);
            }
            List<Report> reports = new ArrayList<>();
            Map<String, Ast.FnDef> values = db.ask(new Bodies.Helpers(name)).value();
            for (Diagnostic failure : souther.compiler.ExampleVerifier.check(rows, scope.value(),
                    sigs.value(), classes, loader(db, Map.of()),
                    values == null ? Map.of() : values)) {
                reports.add(Report.of(failure));
            }
            return reports.isEmpty() ? Answer.of(Boolean.TRUE) : Answer.absent(reports);
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
