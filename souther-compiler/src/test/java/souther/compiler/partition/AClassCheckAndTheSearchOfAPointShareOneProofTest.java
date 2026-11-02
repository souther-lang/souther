package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a class a line cuts lies outside the case, and the search for a row at the same point,
 * are put to one realizer and so prove the same thing once.
 *
 * <p>Read off the proofs the search works out while a whole model is searched. The class check is
 * asked before the search of its point and the search asks the same region the same question, so
 * a proof worked out twice for one region means the two were asked of different realizers — which
 * no answer of the model shows, since both come out the same. Held to a model with one border, whose
 * region no other border shares: where two borders reach one region each of them proves what it is
 * asked, and that is a cost this search accepts for letting the region go with its border.
 *
 * <p>Beside the architecture test that holds who makes a realizer, and not instead of it: that one
 * says where a realizer is made, and this one says the class check and the search were handed the
 * same.
 */
class AClassCheckAndTheSearchOfAPointShareOneProofTest {

    /** A guard on an input, whose line is the behavior's own and is owed a row either side. */
    private static final String GUARDED = """
            module example.guarded

            data Ok
            data No
            data Verdict = Ok | No

            behavior band : (days: Int) -> Verdict
            let band (days) = {
                guard days <= 30 else No
                Ok
            }

            example band
                | "well inside" : (5) -> Ok
            """;

    /** A proof worked out while a search was running, and which region it was worked out for. */
    private record Worked(boolean whileSearching, int region, StandingImpossibility.Asked asked) {}

    @Test
    void aProofIsWorkedOutOnceForTheRegionOfASearchedBorder() {
        List<Worked> worked = Collections.synchronizedList(new ArrayList<>());
        ProofsOfNoValue.WORKED = each -> worked.add(new Worked(whileSearching(),
                System.identityHashCode(each.region()), each.asked()));
        try {
            Compilation compilation = Compilation.ofSource(GUARDED, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertNotNull(Adequacy.generatedOf(compilation.db(), "example.guarded"),
                    "the model under test compiles");
        } finally {
            ProofsOfNoValue.WORKED = null;
        }

        List<Worked> whenSearching = worked.stream().filter(Worked::whileSearching).toList();
        assertFalse(whenSearching.isEmpty(),
                "the search of this model reaches a proof, or this holds nothing: " + worked);
        Map<Worked, Integer> times = new HashMap<>();
        whenSearching.forEach(each -> times.merge(each, 1, Integer::sum));
        Map<Worked, Integer> more = new HashMap<>(times);
        more.values().removeIf(count -> count == 1);
        assertTrue(more.isEmpty(),
                "a proof worked out twice for one region and one question while one border was"
                        + " searched: " + more);
    }

    /** Whether the proof being worked out is one of the search of the borders. */
    private static boolean whileSearching() {
        return StackWalker.getInstance().walk(frames -> frames.anyMatch(each ->
                each.getClassName().equals("souther.compiler.query.Coverages")
                        && each.getMethodName().equals("searched")));
    }
}
