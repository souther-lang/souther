package souther.compiler.conformance;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.test.RepositoryLayout;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Every model this repository carries, compiled and answered.
 *
 * <p>The population a test asks about when its subject is the language rather than one source: the
 * conformance corpora, which are what the language declares it accepts, and the bench corpora, which
 * are models written to be worked with. A test that sweeps positions, rules or readings is asking
 * about all of them, and asking about a smaller set would make its answer one about the fixtures it
 * happened to name.
 *
 * <p><b>Built once for the JVM that asks.</b> Answering these is most of what such a test costs, and
 * a class with three questions about the population would otherwise pay for the population three
 * times. The compilations are handed out to be read: the answers are kept in each one's store, so a
 * second reader finds the questions already put. A caller that would change one — update its
 * documents, give it another budget — makes its own rather than taking these.
 */
public final class RepositoryModels {

    /** The bench corpora, as the files each is compiled from, relative to the repository root. */
    private static final List<List<String>> BENCH = List.of(
            List.of("souther-bench/src/main/resources/souther/bench/corpus/crm/crm.sou",
                    "souther-bench/src/main/resources/souther/bench/corpus/crm/pipeline.sou",
                    "souther-bench/src/main/resources/souther/bench/corpus/crm/quoting.sou"),
            List.of("souther-bench/src/main/resources/souther/bench/corpus/issuetracker/issues.sou"),
            List.of("souther-bench/src/main/resources/souther/bench/corpus/runtime/runtime.sou"));

    private static final List<Compilation> ALL = compileEverything();

    private RepositoryModels() {
    }

    /** Every model this repository carries, each with everything about it answered. */
    public static List<Compilation> all() {
        return ALL;
    }

    private static List<Compilation> compileEverything() {
        List<Compilation> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            // The analysing entry point, which is what says a conformance corpus was analysed: it
            // puts the adequacy questions as well as compiling.
            out.add(corpus.analyse().compilation());
        }
        Path root = RepositoryLayout.ofWorkingDirectory().root();
        for (List<String> corpus : BENCH) {
            List<String> sources = new ArrayList<>();
            for (String each : corpus) {
                sources.add(read(root.resolve(each)));
            }
            Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
            compilation.answerEverything();
            out.add(compilation);
        }
        return List.copyOf(out);
    }

    private static String read(Path source) {
        try {
            return Files.readString(source);
        } catch (IOException e) {
            throw new UncheckedIOException("a corpus this repository carries is not readable: "
                    + source, e);
        }
    }
}
