package souther.compiler.query;

import souther.compiler.conformance.ConformanceCorpus;
import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two stores given the same sources are asked the same questions.
 *
 * <p>What an answer was built from is what an edit is absorbed by, so which questions a compile
 * reaches is as much what it did as what it said: two stores over one input reaching different
 * graphs would mean the dependencies recorded in one are not the ones the other would keep.
 *
 * <p>Its own test rather than a line of the one that compares the answers. That one is about what
 * two stores kept where they were asked the same thing, and it can only be about that once this
 * holds. {@link EverythingAnAnswerHoldsMeansSomethingTest} is where the answers themselves are held
 * to meaning something.
 */
class TwoStoresOverOneInputAreAskedTheSameQuestionsTest {

    @Test
    void bothStoresAreAskedTheSameQuestions() {
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Set<Key<?>> one = corpus.analyse().compilation().db().everyAnswer().keySet();
            Set<Key<?>> other = corpus.analyse().compilation().db().everyAnswer().keySet();
            Set<String> onlyOne = new TreeSet<>();
            one.stream().filter(key -> !other.contains(key))
                    .forEach(key -> onlyOne.add(key.toString()));
            Set<String> onlyOther = new TreeSet<>();
            other.stream().filter(key -> !one.contains(key))
                    .forEach(key -> onlyOther.add(key.toString()));
            assertEquals(Set.of(), onlyOne, "asked only the first time, of " + corpus);
            assertEquals(Set.of(), onlyOther, "asked only the second time, of " + corpus);
        }
    }
}
