package souther.bench;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That every corpus still compiles. The benchmarks themselves are not run here — a shared machine
 * says nothing reliable about how long anything takes — but what they are measured against has to
 * keep working, and a language change that leaves a corpus behind would otherwise be found the next
 * time someone took a measurement and read a faster number as an improvement.
 */
class CorpusTest {

    @Test
    void everyCorpusCompiles() {
        for (Corpus corpus : Corpus.all()) {
            corpus.check(corpus.compile());
        }
    }

    /**
     * That something here is still several sources compiled as one.
     *
     * <p>What a corpus is for is measuring the compiler against a model of the size someone writes,
     * and a model that size is written in several files that name each other. A corpus that lost
     * that — a file dropped, a corpus replaced by a smaller one — would go on compiling and go on
     * being timed, and every question about what happens between two modules would be asked of
     * inputs that have only one. The failure is silent by construction: nothing about a single-file
     * compile looks wrong.
     *
     * <p>What this does not claim: that a body here is spliced across a module. The corpora import
     * each other's types and none of them calls the other's helpers, so nothing measured here
     * exercises a body copied out of another module's file. That is held by
     * {@code ACopiedBodyIsReadAgainstAFileThisCompileHasTest} on a fixture written for it.
     */
    @Test
    void someCorpusIsSeveralSourcesHandedOverAsOneCompile() {
        for (Corpus corpus : Corpus.all()) {
            if (corpus.sources().size() < 2) {
                continue;
            }
            Compilation compilation = corpus.compile();
            if (compilation.modules().size() >= 2) {
                return;
            }
        }
        throw new AssertionError("no corpus hands several sources naming several modules to one"
                + " compile: " + Corpus.all().stream()
                        .map(c -> c + " (" + c.sources().size() + " sources)").toList());
    }

    /** And a corpus of one source is one on purpose, not one that lost its files: it names one
     *  module, so there was never a second file for it to have lost. */
    @Test
    void aCorpusOfOneSourceNamesOneModule() {
        for (Corpus corpus : Corpus.all()) {
            if (corpus.sources().size() == 1) {
                assertTrue(corpus.compile().modules().size() == 1,
                        () -> corpus + " is one source and names several modules");
            }
        }
    }
}
