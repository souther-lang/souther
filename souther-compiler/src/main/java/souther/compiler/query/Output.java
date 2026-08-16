package souther.compiler.query;

import souther.compiler.source.SourceId;

import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.DataChecker;
import souther.compiler.check.Lower;
import souther.compiler.check.ReqSig;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeChecker;
import souther.compiler.check.TypeOps;
import souther.compiler.codegen.Backend;
import souther.compiler.codegen.Emissions;
import souther.compiler.codegen.Instrumentation;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ClassFileDeclarations;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.meta.ModulePath;

import souther.compiler.types.TypeSymbol;

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
            Inputs in = inputs(db, name);
            if (in == null) {
                return Answer.absent();
            }
            try {
                Emissions emitted = Backend.generate(
                        shipped(in), in.scope(), in.typePackages(), in.sigs(), in.imported(),
                        in.injected(),
                        in.callees(), in.requirements(), in.checked(), in.dischargeClauses());
                stamp(db, emitted);
                return Answer.of(Ordered.map(emitted.byBinaryName()));
            } catch (CompileException e) {
                return Answer.absent(e);
            }
        }

        /**
         * The module as what ships carries it: without the methods emitted for its rows' operands.
         *
         * <p>A row runs against {@link Evaluated}'s classes, which keep them; what is written out is
         * the same program less definitions nothing it holds references — an operand's method is
         * reached from a row and from nothing else. Which definitions those are is read off the
         * correspondence the preparation constructed, not off the shape of a name.
         */
        private static Hir.Module shipped(Inputs in) {
            if (in.rowMethods().isEmpty()) {
                return in.lowered();
            }
            List<Hir.FnDef> kept = new ArrayList<>();
            for (Hir.FnDef fn : in.lowered().takenOn()) {
                if (!in.rowMethods().contains(fn.name())) {
                    kept.add(fn);
                }
            }
            return in.lowered().withTakenOn(kept);
        }

        /**
         * The parts of a generation both {@link Classes} and {@link Evaluated} need, asked once.
         *
         * <p>Both answer with a module's bytecode and differ only in whether each arm records that it
         * ran. Two copies of this would be two chances for the measured classes and the shipped ones to
         * stop being the same program, which is the one thing a measurement of them may not do.
         */
        record Inputs(Hir.Module lowered, Symbols scope, Map<String, String> typePackages,
                      Map<String, Sig> sigs, Map<String, Sig> imported, Set<String> injected,
                      Map<String, ReqSig> callees,
                      Map<String, List<BehaviorRequirement>> requirements,
                      Bodies.Elaborated checked,
                      Map<TypeSymbol, List<Hir.InvariantClause>> dischargeClauses,
                      Set<String> rowMethods) {}

        static Inputs inputs(Db db, String name) {
            Answer<Bodies.Elaborated> checked = db.ask(new Bodies.Checked(name));
            Answer<Lower.Lowered> lowering = db.ask(new Bodies.Lowering(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            // The same answer the check read. The backend replays the composition walk and emits
            // the codecs a signature says are needed, so building its own would be the boundary's
            // question answered a third time.
            Answer<Map<String, Sig>> signatures = db.ask(new Bodies.Signatures(name));
            Answer<Map<String, Sig>> imported = db.ask(new Bodies.Imported(name));
            Answer<Set<String>> injected = db.ask(new Bodies.ImportedInjected(name));
            Answer<Map<String, ReqSig>> callees = db.ask(new Bodies.CalleeSigs(name));
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Map<String, List<BehaviorRequirement>>> requirements =
                    db.ask(new Bodies.Requirements(name));
            // A derived decoder maps a clause onto the Raoh constraint that says the same thing, and it
            // is written against the operations an author wrote — which the lowered module no longer has.
            Answer<Map<TypeSymbol, List<Hir.InvariantClause>>> dischargeClauses =
                    db.ask(new Shapes.InvariantsForDischarge(name));
            if (!checked.present() || !lowering.present() || !scope.present() || !imported.present()
                    || !signatures.present() || !injected.present() || !callees.present()
                    || !prepared.present() || !requirements.present() || !dischargeClauses.present()) {
                return null;
            }
            return new Inputs(lowering.value().lowered(), scope.value(),
                    prepared.value().importedFrom(), signatures.value(), imported.value(),
                    injected.value(),
                    callees.value(), requirements.value(), checked.value(), dischargeClauses.value(),
                    Set.copyOf(prepared.value().operandMethods().values()));
        }

        /**
         * Puts this module's declarations on its classes, as its source wrote them.
         *
         * <p>Nothing here can fail in a way worth reporting. A module with no source of its own was
         * read off the path, and its jar was stamped where it was built; and the declarations are
         * only asked for once the module has checked, so they are there.
         */
        private void stamp(Db db, Emissions classes) {
            stamp(db, name, classes);
        }

        /**
         * Puts {@code module}'s declarations on {@code classes}, as its source wrote them.
         *
         * <p>Done for the classes an evaluation runs as well as for the ones that ship, so that the
         * two are the same set of classes and differ only in the counting. A set that ran with one
         * class missing would be a second program, and whether a row holds would be a fact about
         * which of the two it met.
         */
        static void stamp(Db db, String module, Emissions classes) {
            String name = module;
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            SourceId id = layout == null ? null : layout.idOfModule().get(name);
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

    /** How much of what an evaluation goes through is recorded as it goes. */
    public enum CoverageMode {

        /** Nothing. What an evaluation asks for when nobody is measuring it. */
        NONE,

        /** Which arm of each of the module's bodies the rows took. */
        ARMS
    }

    /**
     * One module's classes, counting what they go through — and, where asked, recording which arms
     * they took.
     *
     * <p>Its own key rather than an argument to {@link Classes}, for the reason a probed generation had one:
     * {@link Classes} is what ships, and widening it to mean "counted, sometimes" would put the
     * decision of whether a jar refers to the compiler inside a parameter. These are never stamped and
     * never written out.
     *
     * <p>Counting is not optional the way coverage is. Every evaluation runs against counted classes,
     * because what holds a row to a budget it cannot exceed is the counting itself — a row evaluated
     * against uncounted classes has nothing but a clock behind it.
     *
     * <p>Absent where {@link CoverageMode#ARMS} is asked for and the plan and the bodies do not line
     * up, which is the one thing this must not paper over: emitting a body an arm short reports the
     * arm that ran as one nothing reaches, and that reads as a gap in the model rather than a fault in
     * the measurement.
     */
    public record Evaluated(String name, CoverageMode coverage)
            implements Key<EvaluationArtifact> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<EvaluationArtifact> compute(Db db) {
            Classes.Inputs in = Classes.inputs(db, name);
            if (in == null) {
                return Answer.absent();
            }
            Instrumentation instrumentation = Instrumentation.COUNTING;
            if (coverage == CoverageMode.ARMS) {
                instrumentation = instrumentation.measuring(
                        CoverageSites.of(in.checked().behaviorBodies()));
            }
            try {
                Emissions emitted = Backend.generate(
                        in.lowered(), in.scope(), in.typePackages(), in.sigs(), in.imported(),
                        in.injected(),
                        in.callees(), in.requirements(), in.checked(), in.dischargeClauses(),
                        instrumentation);
                Classes.stamp(db, name, emitted);
                // The classes and what they implement, from the one emission that decided both.
                return Answer.of(new EvaluationArtifact(Ordered.map(emitted.byBinaryName()),
                        emitted.implemented()));
            } catch (CompileException e) {
                return Answer.absent(e);
            } catch (IllegalStateException _) {
                return Answer.absent();   // the plan is not about these bodies
            }
        }

        /** The plan of the same module, for a caller that needs to read what a hit set means. Made
         * from the same answer the classes were generated from, so the numbers agree. */
        public static CoverageSites.Plan planOf(Db db, String module) {
            Bodies.Elaborated checked = db.ask(new Bodies.Checked(module)).value();
            return checked == null ? CoverageSites.Plan.NONE
                    : CoverageSites.of(checked.behaviorBodies());
        }
    }

    /**
     * What an evaluation of one module's rows loads: every module the rows can reach, counted, with
     * arms recorded in the one module a measurement is about.
     *
     * <p>The two scopes differ on purpose, and getting them the same way round is what this key is
     * for. Arms belong to the module whose report reads the numbers, so probing an import would number
     * arms against a plan nothing here can read. A budget belongs to the evaluation, and an evaluation
     * goes wherever the row goes — so a row that steps into an import and loops there has to be
     * counted while it is in there, or the counting stops at the module boundary and the clock decides
     * again.
     *
     * <p>Only the modules this compilation declares are here. A module from the path is not
     * regenerated at all: what a published one carries is what an importer needs to read its
     * declarations, so regenerating it would produce some of its classes and not the rest, and a
     * module split between this set and the parent hands its own types to its own implementation
     * under two definitions of them. {@link #evaluationLoader} takes the path's classes whole and
     * counts them on the way in, so the counting still does not stop at the import.
     */
    public record EvaluationLinked(String name, CoverageMode coverage)
            implements Key<EvaluationArtifact> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<EvaluationArtifact> compute(Db db) {
            List<String> reaches = db.ask(new Reaches(name)).value();
            if (reaches == null) {
                // What this module reaches always includes this module, so there is no such answer.
                // Absent rather than an empty set of classes with an empty manifest beside it: a
                // manifest saying nothing is generated is an answer, and it would tell every row that
                // nothing applies its behavior, which is what a module with no `let` anywhere looks
                // like. Nothing was worked out, so nothing is said.
                return Answer.absent();
            }
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            Map<String, byte[]> linked = new LinkedHashMap<>();
            GeneratedImplementations implemented = null;
            // Furthest first, so the module being evaluated is put on last, as Linked does.
            for (int i = reaches.size() - 1; i >= 0; i--) {
                String reached = reaches.get(i);
                // Only the modules this compilation declares. A module from the path is not generated
                // here at all: what a published one carries is what an importer needs to read its
                // declarations, so regenerating it would produce some of its classes and not the rest
                // — and a module split between this loader and the parent hands its own types to its
                // own implementation under two different definitions of them. The evaluation loader
                // takes the path's classes whole and counts them on the way in.
                if (layout == null || !layout.idOfModule().containsKey(reached)) {
                    continue;
                }
                Answer<EvaluationArtifact> classes = db.ask(new Evaluated(reached,
                        reached.equals(name) ? coverage : CoverageMode.NONE));
                // A module this compilation declares and could not generate makes this absent rather
                // than making the set one class short. Evaluating against a set with a hole in it
                // produces a class that will not load, or a stale one found further up the loader
                // chain, or an example that fails for neither reason — and all three read as a fault
                // in the model.
                if (classes.value() == null) {
                    return Answer.absent(classes.reports());
                }
                linked.putAll(classes.value().classes());
                if (reached.equals(name)) {
                    implemented = classes.value().implementations();
                }
            }
            if (implemented == null) {
                // The module being evaluated was not generated here, so what applies its behaviors is
                // not known — and an evaluation is over its rows. Absent for the reason the loop above
                // is absent one class short: a run given no manifest for it would read every one of
                // its rows as one nothing applies.
                return Answer.absent();
            }
            return Answer.of(new EvaluationArtifact(Ordered.map(linked), implemented));
        }
    }

    /** The class loader compile-time code runs against: this compilation's classes over the ones the
     * projects it depends on already built. */
    static ClassLoader loader(Db db, Map<String, byte[]> classes) {
        ModulePath path = db.ask(new Front.Path()).value();
        ClassLoader parent = path == null ? Output.class.getClassLoader()
                : path.loader(Output.class.getClassLoader());
        return new MemoryClassLoader(classes, parent);
    }

    /**
     * Where this compilation reads declarations of a module from — its own generated classes first,
     * then the path.
     *
     * <p>The same two places the evaluation loader draws classes from, and in the same order, because
     * they are answers to one question: which module a name means here. A reader with only what this
     * compilation generated would find nothing for a module that arrived compiled, which is the
     * ordinary shape of a project rather than an edge of one.
     *
     * <p>Its own first, for the reason the loader has: a module being compiled here wins over one of
     * the same name on the path.
     */
    static ClassFileDeclarations declarationsRead(Db db) {
        Map<String, byte[]> generated = db.ask(new All()).value();
        ModulePath path = db.ask(new Front.Path()).value();
        return new ClassFileDeclarations(binaryName -> {
            byte[] here = generated == null ? null : generated.get(binaryName);
            if (here != null || path == null) {
                return here;
            }
            return path.bytes(binaryName);
        });
    }

    /**
     * The loader an <em>evaluation</em> runs against, where a class read from the path is counted on
     * the way in.
     *
     * <p>A published module carries what an importer needs to read its declarations and no more, so a
     * behavior's body stays in the jar it was built into. Regenerating what does travel and taking
     * the rest from the jar is the one thing that must not be done: a class defined here and one
     * defined by the parent are different types under one binary name, so a module split between them
     * hands its own types to its own implementation and the cast fails — which is reported as an
     * example that does not hold, about a model that is fine.
     *
     * <p>So the path's classes are defined here, whole, with a counted point on every backward
     * branch. One loader, one version of every type, and a row that loops inside a dependency spends
     * the budget there rather than running until the wait ends.
     */
    static ClassLoader evaluationLoader(Db db) {
        ModulePath path = db.ask(new Front.Path()).value();
        ClassLoader compiler = Output.class.getClassLoader();
        if (path == null) {
            return compiler;
        }
        return new ClassLoader(compiler) {
            @Override
            protected Class<?> findClass(String name) throws ClassNotFoundException {
                byte[] bytes = path.bytes(name);
                if (bytes == null) {
                    throw new ClassNotFoundException(name);
                }
                byte[] counted = souther.compiler.evaluate.Recounted.of(bytes);
                return defineClass(name, counted, 0, counted.length);
            }
        };
    }

    /** How long this compilation gives one row or one reading, in milliseconds. A compilation that
     * says nothing is given the default, which is what a build wants; the input exists for a caller
     * whose reason to differ is its own (see {@link Front.ExampleBudget}). */
    static long exampleBudgetMs(Db db) {
        Long asked = db.ask(new Front.ExampleBudget()).value();
        return asked == null ? policyOf(db).outerTimeout().toMillis() : asked;
    }

    /**
     * What this compilation allows one row's evaluation.
     *
     * <p>Read from the compilation rather than from a system property at the point of use, so that two
     * compiles in one JVM may differ and so that a long-lived one — a build daemon, an editor's
     * language server — is not held for its whole life to whatever the first compile in it read.
     */
    public static souther.compiler.examples.EvaluationPolicy policyOf(Db db) {
        souther.compiler.examples.EvaluationPolicy said = db.ask(new Front.Policy()).value();
        return said == null ? souther.compiler.examples.EvaluationPolicy.DEFAULT : said;
    }

    /**
     * What this compilation gives one row or one reading to finish within.
     *
     * <p>A deadline set outright wins over a budget in milliseconds, and only a test sets one: what
     * it is for is stating that a particular row does not come back, rather than writing a model
     * that does not come back and racing a clock to observe it.
     */
    static souther.compiler.examples.Deadline deadlineOf(Db db) {
        souther.compiler.examples.Deadline said = db.ask(new Front.ExampleDeadline()).value();
        return said != null ? said
                : souther.compiler.examples.Deadline.ofMillis(exampleBudgetMs(db),
                        policyOf(db).workerStackBytes());
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
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!prepared.present() || !scope.present()) {
                return Answer.absent();
            }
            List<DataChecker.ConstCheck> checks;
            try {
                checks = DataChecker.constNewtypeChecks(prepared.value().fns(), scope.value());
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
                    ctfe = Class.forName(SoutherJvmAbi.nameOf(new GeneratedClass.Ctfe(
                            new GeneratedClass.Value(check.type()))).binaryName(), true, loader);
                    holds = (boolean) ctfe.getMethod("check", paramClass(check.value()))
                            .invoke(null, check.value());
                } catch (ReflectiveOperationException | LinkageError _) {
                    continue;   // cannot evaluate at compile time; the run-time check still applies
                }
                if (!holds) {
                    String shown = check.typeName() + "("
                            + (check.value() instanceof String s ? "\"" + s + "\"" : check.value()) + ")";
                    String clause = failingClause(db, check, ctfe);
                    reports.add(Report.raised(Diagnostic.at(check.pos())
                                    .say(clause == null
                                            ? new DataMessage.TheWrittenValueViolatesTheInvariant(
                                                    shown)
                                            : new DataMessage.TheWrittenValueViolatesTheClause(
                                                    shown, clause))
                                    .build()));
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
            Answer<souther.compiler.check.Prepared> declaring = db.ask(new Shapes.Prepared(check.type().module()));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(check.type().module()));
            if (!declaring.present() || !scope.present()) {
                return null;
            }
            List<Hir.InvariantClause> clauses = null;
            for (souther.compiler.check.Derived.Def declared : declaring.value().defs()) {
                if (declared.read() instanceof Hir.Data d && d.name().equals(check.type().name())) {
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
     * Every input for which two of a module's written statements about one behavior answer
     * differently — a {@code fake} row or a {@code with} against an {@code example} row that records
     * what the behavior owes.
     *
     * <p>Asked of the module and not of a source, because the two sides of one disagreement need not
     * be in one file: a module's fakes are what its attached files' rows run against and the other way
     * round. Each source's key projects the ones written in it ({@link SaidDisagreements}), so one
     * disagreement is said at both of the places it is written and computed once.
     *
     * <p>The answer is what the check came to and not the disagreements alone: a statement that could
     * not be read within its budget is a statement nothing was decided about, and a bare list of
     * disagreements says that with the same empty list it says agreement with.
     */
    public record Disagreements(String name)
            implements Key<souther.compiler.examples.ExampleStatements.Readings> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<souther.compiler.examples.ExampleStatements.Readings> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            if (!db.ask(new Bodies.Checked(name)).present()) {
                // a module that did not check states nothing yet
                return Answer.of(souther.compiler.examples.ExampleStatements.Readings.NONE);
            }
            // The classes alone: nothing here applies a behavior, so what the compile implemented is
            // not a question this asks.
            EvaluationArtifact artifact =
                    db.ask(new EvaluationLinked(name, CoverageMode.NONE)).value();
            Map<String, byte[]> classes = artifact == null ? null : artifact.classes();
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(name)).value();
            if (classes == null || requirements == null) {
                return Answer.absent();
            }
            Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(name)).value();
            // `requirements` is asked for above as a readiness condition — a module whose
            // requirements are not settled is not one to read statements off yet — rather than
            // because reading them needs it. Nothing here applies a behavior.
            return Answer.of(souther.compiler.examples.ExampleStatements.disagreements(
                    prepared.value().forExamples(),
                    scope.value(), sigs.value(), classes, evaluationLoader(db),
                    values == null ? Map.of() : values, deadlineOf(db), policyOf(db)));
        }
    }

    /**
     * The module's disagreements ({@link Disagreements}), said.
     *
     * <p>One disagreement is one warning. It is anchored at the recorded row and points at the
     * stand-in, and it is said at both of the sources they are written in, so an author editing
     * either file is told. Which of the two carries the caret is not a claim that the other is the
     * one in the wrong; it is where a reader starts reading, and the message names both.
     *
     * <p>Its own key rather than a second thing {@link Examples} says. That key answers what a
     * source's rows turned out to be, and it goes absent for reasons that have nothing to do with
     * what two statements say about each other — a name the source declares twice, a dependency list
     * that could not be read — and took these with it. Asked of the module and not of a source,
     * because one disagreement is one thing to say and its two sides need not be in one file. The
     * value is {@code true} and the reports are the answer, as {@code Adequacy.Warnings} is.
     *
     * <p>What is still needed is a module that checks and links: no behavior is applied, but building
     * a fixture runs the decoders its types derive and the helpers it applies, and those are classes
     * this compile generated. So a module with a type error says nothing here — its rows say nothing
     * anywhere yet — and a batch compile that stops at the first error never asks.
     *
     * <p>A warning. The two contradict, and which of them the model is to be held to is not readable
     * from the text — that would be a claim about which side is derived from the other, and neither
     * is.
     *
     * <p>A fake whose table could not be read in time is a warning of its own (E1920): what it and
     * the rows state was not compared, which is not what saying nothing means here.
     */
    public record SaidDisagreements(String name) implements Key<Boolean> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            souther.compiler.examples.ExampleStatements.Readings read =
                    db.ask(new Disagreements(name)).value();
            if (read == null) {
                return Answer.of(true);
            }
            List<Report> reports = new ArrayList<>();
            // Each is filed under the source its own caret is in, which is what a report with
            // nothing beside its place is filed under.
            for (souther.compiler.examples.ExampleStatements.Disagreement d : read.disagreements()) {
                reports.add(Report.of(said(d)));
            }
            for (souther.compiler.examples.ExampleStatements.UnreadFake f : read.unread()) {
                reports.add(Report.of(unread(f)));
            }
            return Answer.of(true, reports);
        }

        /** One fake that could not be read: the caret on the behavior it names, and what stopped. */
        private static Diagnostic unread(souther.compiler.examples.ExampleStatements.UnreadFake f) {
            // Which of the three it was travels into the message, because what to do about them
            // differs — and one of them is not about the model at all.
            souther.compiler.examples.ExampleStatements.Unread why = f.why();
            Diagnostic.Builder said = Diagnostic.at(f.at(), f.width())
                    .say(why.isDepth()
                            ? new ExampleMessage.NotComparedTheTableReachedItsDepthLimit(
                                    f.target(), why.limitShown())
                            : why.isSteps()
                                    ? new ExampleMessage.NotComparedTheTableSpentItsSteps(
                                            f.target(), why.limitShown())
                                    : why.isStack()
                                            ? new ExampleMessage.NotComparedTheTableRanOutOfStack(
                                                    f.target(), why.limitShown())
                                            : new ExampleMessage.NotComparedTheTableDidNotAnswer(
                                                    f.target(), why.limitShown()));
            return (why.isDepth()
                    ? said.hint(new ExampleMessage.TheTableComparedRecursesTooDeeply(f.target()))
                    : why.isSteps()
                    ? said.hint(new ExampleMessage.TheTableComparedGoesRoundTooManyTimes(f.target()))
                    : why.isStack()
                    ? said.hint(new ExampleMessage.TheStackGotThereFirstWhenComparing(f.target()))
                    : said.hint(new ExampleMessage.NotAnsweringIsNotTwoAnswers(f.target())))
                    .build();
        }

        /** One disagreement: the caret on the recorded row, a second region on the stand-in in
         * whichever file it was written in, and what each of them answers. */
        private static Diagnostic said(souther.compiler.examples.ExampleStatements.Disagreement d) {
            souther.compiler.examples.ExampleStatements.Statement recorded = d.recorded();
            souther.compiler.examples.ExampleStatements.Statement standIn = d.standIn();
            boolean viaWith = d.viaWith();
            // The region says which file it is in, and whether that is worth printing is the
            // renderer's — it already leaves the name out where it matches the one in the heading.
            // Deciding it here meant naming the source a second time beside a region that carries
            // one, which is two answers to one question and the shape #760 was.
            return Diagnostic.at(recorded.region())
                    .say(viaWith
                            ? new ExampleMessage.TheRowAndTheWithDisagree(d.behavior())
                            : new ExampleMessage.TheRowAndTheFakeDisagree(d.behavior()))
                    .secondary(standIn.region(),
                            viaWith ? new ExampleMessage.TheWithIsHere(d.behavior())
                                    : new ExampleMessage.TheFakeRowIsHere(d.behavior()))
                    .hint(viaWith
                            ? new ExampleMessage.WhatTheRowSaysAndWhatTheWithSays(recorded.answer(),
                                    standIn.answer())
                            : new ExampleMessage.WhatTheRowSaysAndWhatTheFakeSays(recorded.answer(),
                                    standIn.answer()))
                    .build();
        }
    }

    /**
     * The examples of one module, evaluated. Every module's examples are evaluated before any
     * failure stops a compile, so a change to a widely-imported data says how far it reaches in one
     * compile rather than one module per round.
     */
    public record Examples(String name, SourceId sourceId, CoverageMode coverage)
            implements Key<Examples.Of> {

        /**
         * The rows of one source, run the one way this compilation runs them.
         *
         * <p>Which mode is derived here rather than chosen by the caller, so that a compile evaluates
         * its rows once. What a measurement needs beyond a compile is the arms each row took, and
         * asking for that as a second key ran every row a second time — against different bytecode,
         * on a second wait, with a second chance to be reported differently. Two sets of outcomes for
         * one model can disagree, and a report built half from each says a case is verified and its
         * branch unreached in the same breath.
         *
         * <p>Keyed on what is actually emitted rather than on the adequacy level, because two levels
         * that measure the same thing should not be two compiles.
         */
        public static Examples asked(Db db, String name, SourceId sourceId) {
            return new Examples(name, sourceId, Adequacy.coverageAsked(db));
        }

        /**
         * What this source's rows turned out to be.
         *
         * <p>The answer carries a value even when rows failed, because a failing row is still an
         * observation: it says which case the behavior actually produced, and which inputs were legal.
         * An answer that went absent on the first failure would leave every adequacy measure reading
         * nothing and reporting gaps that the rows in front of it already covered.
         */
        public record Of(List<souther.compiler.observe.RowOutcome> rows,
                         List<souther.compiler.observe.Incompleteness> incompleteness) {

            public static final Of NONE = new Of(List.of(), List.of());

            public Of {
                rows = List.copyOf(rows);
                incompleteness = List.copyOf(incompleteness);
            }
        }

        @Override
        public String module() {
            return name;
        }

        @Override
        public SourceId sourceId() {
            return sourceId;
        }

        /**
         * The rows this source wrote, run — and the fakes it wrote, built.
         *
         * <p>The fakes here rather than in {@link #evaluate}, which a measurement runs a second time
         * against instrumented classes. Whether a table can be built
         * is not a question a measurement asks, and asking it twice would have one table answered for
         * by two builds.
         */
        @Override
        public Answer<Of> compute(Db db) {
            Answer<Of> ran = evaluate(db, name, sourceId,
                    db.ask(new EvaluationLinked(name, coverage)).value(), coverage);
            List<Diagnostic> wrong = fakeTables(db, name, sourceId);
            if (wrong.isEmpty()) {
                return ran;
            }
            List<Report> reports = new ArrayList<>(ran.reports());
            for (Diagnostic d : wrong) {
                reports.add(Report.of(d));
            }
            return new Answer<>(ran.value(), reports);
        }

        /**
         * What building the fakes written in this source says about them.
         *
         * <p>Every fake it wrote, whether or not a row reaches one. A fake is a statement about the
         * behavior it stands in for the way a row is, and the two other places a table is built each
         * need something else to be there — a row of a behavior that depends on the faked one
         * ({@code resolveFake}), or a row recorded for the faked one itself (the reading behind
         * {@link Disagreements}) — so a module that writes neither had its table built nowhere.
         *
         * <p>Which source wrote which fake is passed rather than used here: which of two tables
         * written for one dependency answers is a fact about the module, so the reading that knows
         * that is the one that picks what this source's share of them is.
         */
        private static List<Diagnostic> fakeTables(Db db, String name, SourceId sourceId) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return List.of();
            }
            if (!db.ask(new Bodies.Checked(name)).present()) {
                return List.of();   // a module that did not check has nothing to build a value with
            }
            // As above: building a table applies no behavior, so only the classes are read.
            EvaluationArtifact artifact =
                    db.ask(new EvaluationLinked(name, CoverageMode.NONE)).value();
            Map<String, byte[]> classes = artifact == null ? null : artifact.classes();
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(name)).value();
            if (classes == null || requirements == null) {
                return List.of();
            }
            Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(name)).value();
            // As above: `requirements` says this module is ready to be read, not what to read.
            return souther.compiler.examples.ExampleStatements.fakeTables(
                    prepared.value().forExamples(), scope.value(),
                    sigs.value(), classes, evaluationLoader(db),
                    values == null ? Map.of() : values, sourceId,
                    deadlineOf(db), policyOf(db));
        }

        /**
         * The rows of one source, run against {@code classes}.
         *
         * <p>Which classes is the only thing that varies between running rows to compile a module and
         * running them to measure it, and it is passed in rather than decided here so the two cannot
         * become two evaluations. A row that held under one and failed under the other would be a
         * difference in the measurement, not in the model, and the report has no way to tell.
         */
        static Answer<Of> evaluate(Db db, String name, SourceId sourceId, EvaluationArtifact artifact,
                                   CoverageMode coverage) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            if (!db.ask(new Bodies.Checked(name)).present()) {
                return Answer.absent();   // a module that did not check has nothing to run
            }
            if (artifact == null) {
                // Arms were asked for and the instrumented classes could not be made. Falling back to
                // uncounted ones is not open: what holds a row to a budget is the counting, so a row
                // run against them would be back on the clock. Nothing was observed, and that travels
                // in the channel every other reason travels in.
                return coverage == CoverageMode.NONE ? Answer.absent()
                        : Answer.of(new Of(List.of(), List.of(
                                souther.compiler.observe.Incompleteness.of(
                                        souther.compiler.observe.Incompleteness.Code.INSTRUMENTATION_ABSENT,
                                        souther.compiler.observe.Incompleteness.Scope.MODULE, name))));
            }
            souther.compiler.check.Prepared.ExampleExecution rows =
                    prepared.value().forExamplesWrittenIn(sourceId);
            if (rows.examples().isEmpty()) {
                return Answer.of(Of.NONE);
            }
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(name)).value();
            if (requirements == null) {
                return Answer.absent();
            }
            List<Report> reports = new ArrayList<>(alreadyDeclared(db, name, sourceId));
            if (!reports.isEmpty()) {
                return Answer.absent(reports);   // a row naming one would read the other declaration
            }
            Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(name)).value();
            souther.compiler.examples.ExampleVerifier.Observations observed =
                    souther.compiler.examples.ExampleVerifier.check(rows, scope.value(), sigs.value(),
                            artifact,
                            // What this compile can read declarations of, for holding an answer's own
                            // against. Asked for only if something has to be held: a compile's own
                            // answers are of the module being evaluated by being of this compile of
                            // it, and every answer this run has is one of those today.
                            () -> declarationsRead(db),
                            requirements, evaluationLoader(db),
                            values == null ? Map.of() : values, deadlineOf(db),
                            policyOf(db),
                            // What applies a behavior here is what this compile emitted. A compile has
                            // nothing else to run a row against; something supplied from outside one
                            // arrives through the same seam and brings its own classes.
                            souther.compiler.examples.Answering.generatedHere());
            for (Diagnostic failure : observed.failures()) {
                reports.add(Report.of(failure));
            }
            return Answer.of(new Of(observed.rows(), observed.incompleteness()), reports);
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
        private static List<Report> alreadyDeclared(Db db, String name, SourceId sourceId) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            if (layout == null || sourceId.equals(layout.idOfModule().get(name))) {
                return List.of();   // the module's own source declares what it declares
            }
            Set<String> taken = new LinkedHashSet<>(declaredIn(db, layout.idOfModule().get(name)));
            List<Report> reports = new ArrayList<>();
            for (SourceId id : layout.exampleFilesOf().getOrDefault(name, List.of())) {
                CstFrontend.Parsed parsed = db.ask(new Front.Parsed(id)).value();
                if (parsed == null) {
                    continue;
                }
                for (Ast.FnDef value : parsed.module().fns()) {
                    boolean fresh = taken.add(value.name());
                    if (!fresh && id.equals(sourceId)) {
                        reports.add(Report.of(Diagnostic.at(value.written().reportedAt())
                                .say(new ExampleMessage.TheNameIsAlreadyDeclared(value.name(), name))
                                .build()));
                    }
                }
                if (id.equals(sourceId)) {
                    break;   // the files after this one are their own key's to report
                }
            }
            return reports;
        }

        /** The names the values of one source declare, or none where nothing parsed it. */
        private static Set<String> declaredIn(Db db, SourceId id) {
            Set<String> names = new LinkedHashSet<>();
            CstFrontend.Parsed parsed = id == null ? null : db.ask(new Front.Parsed(id)).value();
            if (parsed != null) {
                for (Ast.FnDef fn : parsed.module().fns()) {
                    names.add(fn.name());
                }
            }
            return names;
        }

    }
}
