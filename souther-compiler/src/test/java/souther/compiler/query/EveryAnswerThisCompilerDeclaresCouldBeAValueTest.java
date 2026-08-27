package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What every question declares it answers with could be compared as a value, and what could not is
 * written down.
 *
 * <p><b>Quantified over what the compiler declares, not over what a run reached.</b> A store holds
 * whatever a corpus made it hold, so a question no operation of this project puts is outside every
 * check made of a store — and what a declaration allows is wider than what any one compile built.
 * Neither of those is a hole a better corpus closes: the first is about which questions are asked,
 * and the second is about what a question would be allowed to answer with if it were.
 *
 * <p>Which is why this and {@link EverythingAnAnswerHoldsMeansSomethingTest} are two claims and not
 * one written twice. They meet at what a finding <em>is</em>, which {@link AnswerClosure} settles
 * once for both; they part at what they quantify over. A thing handed to a compilation that no
 * corpus sets is met here and nowhere else.
 *
 * <p>It stops where an equality stops, for the reason the walk of a store does: what is under a type
 * that says nothing by {@code equals} is unreachable through an equality that never holds, and
 * naming it too would be naming the consequences of what has already been named.
 */
class EveryAnswerThisCompilerDeclaresCouldBeAValueTest {

    /**
     * Every question this compiler declares, and nothing about how far the scan got.
     *
     * <p>Asked here as well as where the vocabulary is counted, because a scan that fell short
     * leaves this checking a world one question smaller and saying so nowhere.
     */
    private static List<Class<?>> questions() throws Exception {
        Covered<Class<?>> scanned = DeclaredQuestions.scan();
        assertEquals(List.of(), switch (scanned) {
            case Covered.Whole<Class<?>> _ -> List.of();
            case Covered.Partly<Class<?>>(List<Class<?>> _, List<Gap> gaps) -> gaps;
        }, "a class the scan could not load, so what is checked below is not the vocabulary");
        return DeclaredQuestions.found(scanned);
    }

    /**
     * The walk reaches the declarations this is about.
     *
     * <p>The control the assertion below needs. Every question walked without meeting anything says
     * the same thing as a walk that stopped at the first member of every answer, and the difference
     * is the whole of what is being claimed.
     */
    @Test
    void theWalkReachesWhatTheseQuestionsDeclare() throws Exception {
        List<Class<?>> questions = questions();

        assertTrue(questions.size() > 100,
                () -> "a vocabulary of " + questions.size() + " is not this compiler's");
        assertTrue(DeclaredAnswerWalk.of(questions).stream()
                        .anyMatch(each -> each.place().question().endsWith("Output$Classes")),
                "the walk did not reach what a module compiles to, which is the shape it is about");
    }

    /** And what it finds is the places written down, and no others. */
    @Test
    void theOnlyDeclarationsThatCouldNotBeAValueAreTheOnesWrittenDown() throws Exception {
        Set<TypePath.Place> found = new LinkedHashSet<>();
        DeclaredAnswerWalk.of(questions()).forEach(each -> found.add(each.place()));
        Map<TypePath.Place, String> reasons = AnswerClosure.declaredReasons();

        assertEquals(new java.util.HashSet<>(AnswerClosure.declaredPlaces()),
                new java.util.HashSet<>(found),
                () -> "a place a question declares that cannot be compared as a value. What each "
                        + "written-down place is: " + reasons);
    }
}
