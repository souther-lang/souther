package souther.bench;

import org.junit.jupiter.api.Test;

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
}
