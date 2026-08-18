package souther.compiler.examples;

import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ExampleRuns;
import souther.compiler.query.Output;
import souther.compiler.query.Shapes;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * A model's {@code example} rows, and the implementations they can be run against.
 *
 * <p>The source is read at the time the run happens, which is what this is for: an implementation
 * supplied from outside was compiled against a module's classes as some earlier build emitted them,
 * and holding it to the {@code .sou} as it stands now is how a model that moved is found out. Rows
 * travelling with the classes would verify an edited model against its own old record and go quietly
 * green.
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
    private final String module;
    private final Prepared.ExampleExecution rows;
    private final Map<String, Sig> sigs;

    private SoutherExamples(Compilation compilation, String module) {
        this.compilation = compilation;
        this.module = module;
        this.rows = compilation.db().ask(new Shapes.Prepared(module)).value().forExamples();
        this.sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
    }

    /** The rows written in {@code source}. */
    public static SoutherExamples of(Path source) {
        String written;
        try {
            written = Files.readString(source);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return of(written, nameOf(source), source.toString());
    }

    /** The rows written in {@code source}, which is the text of a module rather than a file. */
    public static SoutherExamples ofSource(String source) {
        return of(source, "Main", "the source given");
    }

    private static SoutherExamples of(String written, String fallbackName, String shown) {
        Compilation compiled = Compilation.ofSource(written, fallbackName);
        compiled.db().ask(new Output.All());
        refuseIfItDoesNotCompile(compiled, shown);
        return new SoutherExamples(compiled, compiled.modules().get(0));
    }

    /**
     * These rows, with {@code implementation} answering for whatever behavior it implements.
     *
     * <p>The instance and nothing else. Which behavior it is for is settled by the binary name the
     * ABI gives that behavior's base, looked for in the instance's supertypes; which declarations it
     * reads values by is read from its own loader's class files. Naming either of them here would be
     * a second speller of a rule that has one, and a way to state it wrongly.
     */
    public BoundExamples bind(Object implementation) {
        if (implementation == null) {
            throw new IllegalArgumentException("a binding is of an implementation");
        }
        List<String> bound = new ArrayList<>();
        for (String behavior : sigs.keySet()) {
            if (BoundImplementation.isFor(implementation, module, behavior)) {
                bound.add(behavior);
            }
        }
        if (bound.isEmpty()) {
            throw new IllegalArgumentException(implementation.getClass().getName()
                    + " implements no behavior of `" + module + "`");
        }
        return new BoundExamples(this, ExampleRuns.evaluating(compilation.db(), module,
                Answering.bound(implementation, sigs)), bound);
    }

    Prepared.ExampleExecution module() {
        return rows;
    }

    /** The module the rows are of. */
    public String moduleName() {
        return module;
    }

    private static String nameOf(Path source) {
        String file = source.getFileName().toString();
        int dot = file.lastIndexOf('.');
        return dot <= 0 ? file : file.substring(0, dot);
    }

    /**
     * A model that did not compile has no rows to run.
     *
     * <p>Refused here rather than left to show up as every row failing: what a row would be held to
     * was never emitted, and a caller told "the row did not hold" would be told the wrong thing
     * about a source that is wrong somewhere else.
     */
    private static void refuseIfItDoesNotCompile(Compilation compiled, String shown) {
        List<String> said = new ArrayList<>();
        for (List<Located> perSource : compiled.diagnostics().values()) {
            for (Located filed : perSource) {
                if (filed.diagnostic().severity() == Severity.ERROR) {
                    said.add(String.valueOf(filed.diagnostic().code()));
                }
            }
        }
        if (!said.isEmpty()) {
            throw new IllegalStateException(shown + " does not compile: " + said);
        }
    }
}
