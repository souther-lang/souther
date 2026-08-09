package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A "did you mean" names the same candidate however the candidates were handed over.
 *
 * <p>The collections a caller offers carry no order anyone chose: the names bound at a point come
 * from an immutable copy, whose iteration order the JVM salts per run, and an import alias reaches
 * the qualifier list through another. Two candidates the same distance from the misspelling are
 * equally good answers, so whichever the loop met first was the answer — and the same source got a
 * different hint on a different run.
 *
 * <p>Asserted as invariance under permutation rather than by compiling the same source many times.
 * A test that compiles and looks at the hint is asking which way the salt fell, and passes about
 * half the time whether the selection is canonical or not.
 */
class ASuggestionDoesNotDependOnTheOrderCandidatesAreOfferedInTest {

    /** Both are one edit from `aac`, and neither is the name itself. */
    private static final List<String> TIED = List.of("aaa", "aab");
    private static final List<String> TIED_REVERSED = List.of("aab", "aaa");

    @Test
    void namesTheSameCandidateWhicheverOrderTheTiedOnesArrivedIn() {
        assertEquals(Suggest.candidate("aac", TIED), Suggest.candidate("aac", TIED_REVERSED));
    }

    @Test
    void breaksATieByName() {
        assertEquals("aaa", Suggest.candidate("aac", TIED_REVERSED));
    }

    @Test
    void answersWhatTheNearestOfOneAnswers() {
        // The two ways of asking for the closest candidate are one question. The bound is written
        // here rather than read from the class, and 2 is what an identifier is matched under, so
        // the two are asked under the same closeness.
        assertEquals(Suggest.nearest("aac", TIED_REVERSED, 2, 1).getFirst(),
                Suggest.candidate("aac", TIED_REVERSED));
    }

    /** A tie is what the order reaches; the answer where there is no tie is unchanged. */
    @Test
    void stillNamesTheOneNearestCandidate() {
        assertEquals("amount", Suggest.candidate("amont", List.of("quantity", "amount", "price")));
    }
}
