package souther.compiler.conformance;

import org.junit.jupiter.api.Test;

import souther.compiler.check.PathReachability;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No proof this compiler makes that nothing arrives somewhere is one a row of a conformance corpus
 * went against.
 *
 * <p>Three kinds of proof, and a run shows each of them wrong the same way: a row through an arm
 * proven shut, a row bringing a comparison out a way proven to come out so for nothing, a row at a
 * comparison proven to be arrived at by nothing. What the reading of the run keeps of them
 * ({@link PathReachability.Answers.AsRun#contradicted}) is where that shows, so over the corpora,
 * where the rows are run, it is empty for every behavior — and a reading that came to state more of
 * a condition than the condition says would show here as a proof a row went against.
 *
 * <p>What it does not establish is the other half. A place no row went to is not shown unreachable
 * by that, and nothing here asks whether a proof that held over these rows holds over every input.
 */
@ClosedWorldContract
class NoProofOfReachIsOneARowWentAgainstTest {

    @Test
    void noRowWentAgainstAProofThatNothingArrives() {
        List<String> wrong = new ArrayList<>();
        int read = 0;
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Compilation compilation = corpus.analyse().compilation();
            for (String module : compilation.modules()) {
                Map<String, PathReachability.Answers.AsRun> arrived =
                        compilation.db().ask(new Adequacy.Arrived(module)).value();
                if (arrived == null) {
                    continue;
                }
                for (Map.Entry<String, PathReachability.Answers.AsRun> each
                        : arrived.entrySet()) {
                    read++;
                    if (!each.getValue().contradicted().isEmpty()) {
                        wrong.add(corpus.name() + " " + module + "." + each.getKey() + ": "
                                + each.getValue().contradicted());
                    }
                }
            }
        }
        assertTrue(read > 0, "the corpora's behaviors were read as run, so the census counted"
                + " something");
        assertEquals(List.of(), wrong, "a row went where this compiler proved nothing arrives, so"
                + " the proof is wrong");
    }
}
