package souther.compiler.examples;

import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.ExampleRuns;
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
        return new SoutherExamples(compiled);
    }

    /**
     * These rows, with {@code implementation} answering for whatever behavior it implements.
     *
     * <p>The instance and nothing else. Which behavior it is for is settled by the binary name the
     * ABI gives that behavior's base, looked for in the instance's supertypes; which declarations it
     * reads values by is read from its own loader's class files. Naming either of them here would be
     * a second speller of a rule that has one, and a way to state it wrongly.
     *
     * <p>Which module the rows are of comes from the same answer. A source set may declare more than
     * one, and taking the first would bind a model by the order its files were handed over.
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
        Prepared.ExampleExecution rows = compilation.db()
                .ask(new Shapes.Prepared(module)).value().forExamples();
        return new BoundExamples(module, rows, ExampleRuns.evaluating(compilation.db(), module,
                Answering.bound(implementation, sigs.get(module))), bound);
    }

    /** The modules these sources declare. */
    public List<String> modules() {
        return List.copyOf(sigs.keySet());
    }

    /**
     * What one row or one observation is given to finish within, from here on.
     *
     * <p>A caller has a reason to say where a compile does not: what a bound implementation waits
     * for is a database, a socket or a filesystem, and how long that may take is theirs to know. The
     * default is set so that no row a model states reaches it, which is a statement about evaluating
     * a `let` body and not about an implementation that went to look something up.
     *
     * <p>Said about these sources and no others, so one caller's budget does not hold every compile
     * in the JVM to it.
     */
    public SoutherExamples withBudget(java.time.Duration budget) {
        compilation.withExampleBudget(budget);
        return this;
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
