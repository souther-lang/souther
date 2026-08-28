package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.execute.ExampleExecution;
import souther.compiler.execute.jvm.JvmExampleRuns;
import souther.compiler.query.ExampleExecutions;
import souther.compiler.query.Output;
import souther.compiler.query.Shapes;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A model's {@code example} rows, and the implementations they can be run against.
 *
 * <p>The source is read at the time the run happens, which is what this is for: an implementation
 * supplied from outside was compiled against a module's classes as some earlier build emitted them,
 * and holding it to the {@code .sou} as it stands now is how a model that moved is found out. Rows
 * travelling with the classes would verify an edited model against its own old record and go quietly
 * green.
 *
 * <p>What is read is a source set and a dependency path, because that is what a model is. A module
 * may write its rows beside itself and in an {@code examples for} file, and may import another
 * user module whose classes a dependency published — so a face taking one file and no path would be
 * narrower than the language, and a project using either would find its rows unreachable rather than
 * failing. Nothing here decides which module the rows are of: {@link #bind} asks the implementation.
 *
 * <p>What holds the two builds together is {@code DeclarationAgreement}, and it is reached on the
 * way to every bound row: an answer states which declarations it reads values by, the two sets are
 * held against each other over what the behavior's crossing reaches, and a row that must not be
 * handed over ends {@code INCOMPLETE} at {@code ANSWERER_ESTABLISHMENT}.
 *
 * <p>There is no JUnit here, no {@code DynamicTest}, no assertion and no lifecycle. This is the
 * enumeration of rows and the evaluation of one; a test framework is its first consumer and is
 * written entirely outside it.
 */
public final class SoutherExamples {

    private final Compilation compilation;

    /** Each module this compile declares, with its signatures. Which of them a binding is of is the
     *  binding's to say, so all of them are kept. */
    private final Map<String, Map<String, Sig>> sigs = new LinkedHashMap<>();

    private SoutherExamples(Compilation compilation) {
        this.compilation = compilation;
        for (String module : compilation.modules()) {
            sigs.put(module, compilation.db().ask(new Bodies.Signatures(module)).value());
        }
    }

    /**
     * The rows written in {@code sources}, resolving imports of other user modules against
     * {@code dependencies}.
     *
     * <p>The whole entrance. A module and its {@code examples for} files are as many sources as they
     * are; what a dependency published is on the path, the way every other reader of a published
     * module reads one.
     */
    public static SoutherExamples of(List<Path> sources, ModulePath dependencies) {
        if (sources.size() == 1) {
            return of(sources.get(0), dependencies);
        }
        Map<String, String> byId = new LinkedHashMap<>();
        for (Path source : sources) {
            byId.put(source.toString(), read(source));
        }
        return settled(Compilation.ofDocuments(byId, Set.of(), dependencies));
    }

    /** The same, of sources that import no other user module. */
    public static SoutherExamples of(List<Path> sources) {
        return of(sources, ModulePath.EMPTY);
    }

    /**
     * The rows written in one file, resolving imports against {@code dependencies}.
     *
     * <p>Its own route and not one file handed to the many-source one. A module written in a single
     * source may leave its {@code module} header off, and what it is called is then the file's own
     * name; linking several sources needs each to say which module it is. Reading a lone file the
     * way several are read would refuse a source the compiler compiles, which is the narrowing this
     * face exists not to do.
     */
    public static SoutherExamples of(Path source, ModulePath dependencies) {
        // Named by its path, so what a refusal says is the file the reader is looking at rather
        // than the number this compile happened to hold it under.
        Compilation compiled = Compilation.ofDocuments(
                Map.of(source.toString(), read(source)), Set.of(), dependencies);
        compiled.db().set(new Front.DefaultName(), nameOf(source));
        return settled(compiled);
    }

    /** The same, of a module written in one file that imports no other user module. */
    public static SoutherExamples of(Path source) {
        return of(source, ModulePath.EMPTY);
    }

    /** The rows written in {@code sources} as text, for a caller holding them rather than files. */
    public static SoutherExamples ofSources(List<String> sources, ModulePath dependencies) {
        return sources.size() == 1
                ? ofSource(sources.get(0), dependencies)
                : settled(Compilation.ofSources(sources, dependencies));
    }

    /** The same, of sources that import no other user module. */
    public static SoutherExamples ofSources(List<String> sources) {
        return ofSources(sources, ModulePath.EMPTY);
    }

    /** One module's text, which may leave its {@code module} header off as a lone file may. */
    public static SoutherExamples ofSource(String source, ModulePath dependencies) {
        return settled(Compilation.ofSource(source, "Main", dependencies));
    }

    /** The same, of one module's text that imports no other user module. */
    public static SoutherExamples ofSource(String source) {
        return ofSource(source, ModulePath.EMPTY);
    }

    private static SoutherExamples settled(Compilation compiled) {
        compiled.db().ask(new Output.All());
        refuseIfItDoesNotCompile(compiled);
        // A row runs on a worker of this compile's own, so what it spends is counted on one thread
        // and how deep it may recurse is this compile's answer; what it hands outside runs on
        // whoever called, because that is the world a supplied implementation answers out of.
        compiled.withDeadline(
                Deadline.crossingBackToTheCaller(Deadline.DEFAULT_WORKER_STACK_BYTES));
        return new SoutherExamples(compiled);
    }

    /**
     * These rows, with {@code implementation} answering for each behavior written without a body
     * that it implements.
     *
     * <p>Written without a body, and said here rather than left to be read off "whatever behavior it
     * implements" — which is the wording this took first, and under which the code went on to answer
     * for a behavior with a `let` as readily as for one without. What a binding makes runnable is the
     * rows that had nothing to run them.
     *
     * <p>The instance and nothing else. Which behavior it is for is settled by the binary name the
     * ABI gives that behavior's base, looked for in the instance's supertypes; which declarations it
     * reads values by is read from its own loader's class files. Naming either of them here would be
     * a second speller of a rule that has one, and a way to state it wrongly.
     *
     * <p>Which module the rows are of comes from the same answer. A source set may declare more than
     * one, and taking the first would bind a model by the order its files were handed over.
     *
     * @throws IllegalArgumentException where the instance implements no behavior of these sources,
     *                                  where it implements behaviors of two modules, or where a
     *                                  behavior it implements has an implementation of its own
     */
    public BoundExamples bind(Object implementation) {
        if (implementation == null) {
            throw new IllegalArgumentException("a binding is of an implementation");
        }
        String module = null;
        List<String> bound = new ArrayList<>();
        for (Map.Entry<String, Map<String, Sig>> declared : sigs.entrySet()) {
            List<String> here = new ArrayList<>();
            for (String behavior : declared.getValue().keySet()) {
                if (BoundImplementation.isFor(implementation, declared.getKey(), behavior)) {
                    refuseIfItHasABody(declared.getKey(), behavior);
                    here.add(behavior);
                }
            }
            if (here.isEmpty()) {
                continue;
            }
            if (module != null) {
                throw new IllegalArgumentException(implementation.getClass().getName()
                        + " implements behaviors of both `" + module + "` and `" + declared.getKey()
                        + "`, and a binding is of one module's rows");
            }
            module = declared.getKey();
            bound = here;
        }
        if (module == null) {
            throw new IllegalArgumentException(implementation.getClass().getName()
                    + " implements no behavior of " + sigs.keySet());
        }
        ExampleExecution asked = ExampleExecutions.of(compilation.db(), module);
        if (asked == null) {
            throw new IllegalStateException("`" + module + "` did not check, so it has no rows to"
                    + " run");
        }
        return new BoundExamples(module, asked.rows(),
                JvmExampleRuns.evaluating(compilation.jvmProgramImages(), asked,
                        compilation.jvmExampleDeadlines().forThisCompile(),
                        Answering.bound(implementation, Set.copyOf(bound), sigs.get(module))),
                bound);
    }

    /**
     * A binding is of an injection target, and of nothing else.
     *
     * <p>What a binding adds is the rows that had nothing to run them. A behavior with a `let` body
     * was runnable before anything was bound, and its rows are run by that body where a compile runs
     * them — so answering one from a supplied instance would not be running a recorded row against
     * an implementation, it would be replacing the model's own with another and reporting the
     * difference as the model's. Whether such a replacement is a thing to offer is its own question,
     * and it is not this one.
     *
     * <p>A behavior Souther is to implement and nobody has is refused for the other reason: no base
     * was emitted for it, because the model says its body is to be written here. An instance offered
     * for one is an instance of something the declaration does not describe.
     *
     * <p>Refused where the binding is made rather than where a row would notice. A caller who bound
     * the wrong instance is told what is wrong with the instance, not told that some row of some
     * behavior did not hold.
     */
    private void refuseIfItHasABody(String module, String behavior) {
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        for (Hir.BehaviorDef declared : prepared.behaviors()) {
            if (!declared.name().equals(behavior)) {
                continue;
            }
            switch (prepared.implementationOf(declared)) {
                case INJECTION_TARGET -> { }
                case IMPLEMENTED -> throw new IllegalArgumentException(
                        "`" + module + "." + behavior + "` has an implementation of its own, so its"
                                + " rows are run by that; a binding is of a behavior written without"
                                + " one");
                case UNIMPLEMENTED -> throw new IllegalArgumentException(
                        "`" + module + "." + behavior + "` is Souther's to implement and has no"
                                + " `let` yet, so its rows are waiting for one; a binding is of a"
                                + " behavior Java supplies");
            }
        }
    }

    /** The modules these sources declare. */
    public List<String> modules() {
        return List.copyOf(sigs.keySet());
    }

    /** What a lone file's module is called when it leaves its `module` header off. */
    private static String nameOf(Path source) {
        String file = source.getFileName().toString();
        int dot = file.lastIndexOf('.');
        return dot <= 0 ? file : file.substring(0, dot);
    }

    private static String read(Path source) {
        try {
            return Files.readString(source);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * A model that did not compile has no rows to run.
     *
     * <p>Refused here rather than left to show up as every row failing: what a row would be held to
     * was never emitted, and a caller told "the row did not hold" would be told the wrong thing
     * about a source that is wrong somewhere else.
     *
     * <p>{@link CompileException} and not a message of this file's own. A caller reaching this is
     * looking at a source of theirs, and what they need is the position, the code and the sentence
     * the compiler already writes — several of them, since a model is wrong where it is wrong.
     * Rebuilding a one-line summary out of codes would take a reader who has all of that and hand
     * them less than the compiler's own entrance does.
     */
    private static void refuseIfItDoesNotCompile(Compilation compiled) {
        List<Located> refusals = new ArrayList<>();
        for (List<Located> perSource : compiled.diagnostics().values()) {
            for (Located filed : perSource) {
                if (filed.diagnostic().severity() == Severity.ERROR) {
                    refusals.add(filed);
                }
            }
        }
        if (!refusals.isEmpty()) {
            throw CompileException.ofAllReported(refusals,
                    "the rows cannot be run: the model they are written in does not compile");
        }
    }
}
