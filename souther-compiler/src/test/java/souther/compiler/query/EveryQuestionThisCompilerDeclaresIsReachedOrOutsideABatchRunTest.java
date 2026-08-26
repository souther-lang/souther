package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.meta.ModulePath;
import souther.compiler.report.GeneratedRows;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every question this compiler declares is one a run over the corpus reaches, or one a batch run has
 * no input for.
 *
 * <p>A question nobody asks is a question nothing checks. What is kept in an answer, whether two
 * compiles of one source answer alike, what a report says — every one of those is held against the
 * answers a run happens to produce, so a family of questions no run reaches is outside all of it and
 * says so nowhere. That is not something the checks themselves can notice: they compare what they
 * found with what is written down, and both are silent about a question that was never put.
 *
 * <p>So the vocabulary is closed from both ends. What the compiler declares is read off the compiled
 * classes rather than off a list somebody maintains — a list is a second truth, and the day a key is
 * added and not registered is the day it says the coverage is whole. What a run reaches is the union
 * of what this project's own operations ask for. Between them:
 *
 * <pre>declared = reached ⊎ what a batch run has no input for</pre>
 *
 * <p>and the union is disjoint, so a question in the second set that a run turns out to reach is a
 * failure as much as one in neither.
 *
 * <p><b>Operations and not questions.</b> What is run below is what this project does — analyse and
 * report, offer rows, ask what a module declares, build at the level a build measures at. Which
 * questions that reaches is the consequence. Written the other way round, with a fixture per key,
 * the suite would be a list of stimuli invented to reach a list, and a question added to one of these
 * operations would arrive uncovered while the arithmetic still added up.
 */
class EveryQuestionThisCompilerDeclaresIsReachedOrOutsideABatchRunTest {

    /**
     * The questions a batch run has no input for.
     *
     * <p>Every one of them takes a place in a text that somebody's cursor is at, or is reached only
     * from one that does. A compilation of a set of sources has no such place, so these are not
     * questions the operations below could be made to reach by writing a better corpus — the input
     * they take does not exist in a batch run at all.
     *
     * <p>What this does not say is that they go unasked. {@code souther-lsp} asks them, and whether
     * that vocabulary is closed the way this one is closed is a question about the editor and is not
     * answered here.
     */
    private static final Set<String> NO_INPUT_IN_A_BATCH_RUN = Set.of(
            "souther.compiler.query.Bodies$ContractCapabilities",
            "souther.compiler.query.Names$Declaration",
            "souther.compiler.query.Names$DeclaredAt",
            "souther.compiler.query.Names$DenotedAt",
            "souther.compiler.query.Names$Reachable",
            "souther.compiler.query.Names$TypeAt",
            "souther.compiler.query.Names$UsesOf",
            "souther.compiler.query.Names$ValueAt",
            "souther.compiler.query.Names$ValueDeclarationsOf",
            "souther.compiler.query.Names$ValueDeclaredAt",
            "souther.compiler.query.Names$ValueDenotedAt",
            "souther.compiler.query.Names$ValueUsesOf",
            "souther.compiler.query.Shapes$InvariantCapabilities");

    /**
     * Every question the compiler declares, discovered from what it compiled to.
     *
     * <p>From the classes and not from a registry. A registry a key has to be added to is a second
     * place to keep in step, and the failure it allows is the one this test exists to prevent: a key
     * added and not registered would leave the arithmetic below adding up while the question went
     * unreached.
     *
     * <p>The code source of {@link Key} and the package it is in, which is where this compiler keeps
     * its query vocabulary. A key declared somewhere else is a change to how the vocabulary is
     * arranged, and this failing to find it is that change being noticed rather than a limit of the
     * scan.
     */
    private static Set<String> declared() throws Exception {
        Path root = Path.of(Key.class.getProtectionDomain().getCodeSource().getLocation().toURI());
        Set<String> out = new TreeSet<>();
        try (Stream<Path> files = Files.walk(root.resolve("souther/compiler/query"))) {
            for (Path each : files.filter(p -> p.toString().endsWith(".class")).toList()) {
                String name = root.relativize(each).toString()
                        .replace(java.io.File.separatorChar, '.')
                        .replaceFirst("\\.class$", "");
                Class<?> type;
                try {
                    type = Class.forName(name, false, Key.class.getClassLoader());
                } catch (Throwable notLoadable) {
                    continue;   // nothing to ask of a class this cannot hold
                }
                if (Key.class.isAssignableFrom(type) && !type.isInterface()
                        && !Modifier.isAbstract(type.getModifiers())) {
                    out.add(type.getName());
                }
            }
        }
        return out;
    }

    /** And every question this project's own operations put over the corpus. */
    private static Set<String> reached() {
        Set<String> out = new TreeSet<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            // Analysing a corpus and writing the report, which is `souther examples`.
            into(corpus.analyse().compilation(), out);

            // Offering an author the rows nothing covers, which is `souther examples --generate`,
            // with and without the rows at the edges a rule draws.
            ConformanceCorpus.Analysed generating = corpus.analyse();
            GeneratedRows.of(generating.compilation(), null, null, true, corpus.names()).text();
            GeneratedRows.of(generating.compilation(), null, null, false, corpus.names()).text();
            into(generating.compilation(), out);

            // Asking a compilation what a module declares, which is what the command line reads to
            // narrow what it is about to do to one behavior.
            ConformanceCorpus.Analysed asking = corpus.analyse();
            asking.compilation().modules()
                    .forEach(module -> asking.compilation().declaredBehaviors(module));
            into(asking.compilation(), out);

            // And a build, which measures what the rows already established and composes no values.
            // Its own operation and not a smaller `souther examples`: what it asks for at a line is a
            // different question from what a search of that line asks.
            into(Compiler.analyzedModules(corpus.sources(), ModulePath.EMPTY, new ArrayList<>(),
                    Adequacy.Asked.warningsAt(Adequacy.Level.WITNESS)), out);
        }
        return out;
    }

    private static void into(Compilation compilation, Set<String> reached) {
        compilation.db().everyAnswer().keySet()
                .forEach(key -> reached.add(key.getClass().getName()));
    }

    @Test
    void whatIsDeclaredAndNotReachedIsExactlyWhatABatchRunHasNoInputFor() throws Exception {
        Set<String> unreached = new TreeSet<>(declared());
        unreached.removeAll(reached());

        assertEquals(new TreeSet<>(NO_INPUT_IN_A_BATCH_RUN), unreached,
                "a question this compiler declares that no run of the corpus asks. Either an"
                        + " operation above is missing one, or the question takes an input a batch"
                        + " run does not have and belongs in the set beside it");
    }

    /**
     * And nothing is in both.
     *
     * <p>The other half of the partition. A question written down as one a batch run cannot put, and
     * then put by one, is a line nobody would ever be made to remove — the set above would go on
     * excusing a question that no longer needs excusing, and the next one filed beside it would
     * inherit the excuse.
     */
    @Test
    void andNothingReachedIsWrittenDownAsOutOfReach() {
        Set<String> both = new TreeSet<>(reached());
        both.retainAll(NO_INPUT_IN_A_BATCH_RUN);

        assertEquals(Set.of(), both,
                "a question a run reaches and this says a batch run has no input for");
    }

    /**
     * And every question a run reaches is one the scan found.
     *
     * <p>What holds the discovery to the vocabulary. A key declared outside the package this scans
     * would leave the arithmetic above adding up over a smaller world, and the question would be
     * unwatched for exactly the reason this test exists.
     */
    @Test
    void andEveryQuestionAskedIsOneTheScanFound() throws Exception {
        Set<String> unknown = new TreeSet<>(reached());
        unknown.removeAll(declared());

        assertEquals(Set.of(), unknown,
                "a question asked whose key the scan of the query package did not find");
    }
}
