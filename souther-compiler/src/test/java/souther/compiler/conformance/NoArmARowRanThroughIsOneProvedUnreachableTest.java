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
 * No arm this compiler proves nothing arrives at is one a row of a conformance corpus ran through.
 *
 * <p>A proof that an arm is unreachable takes it out of what a behavior owes. A row that ran through
 * it shows the proof wrong, and what the reading of the run keeps of such arms
 * ({@link PathReachability.Answers.AsRun#provedWrong}) is where that shows: a measure puts the arm
 * back and says the count is unsettled. So over the corpora, where the rows are run, the set is
 * empty for every behavior, and a reading that came to state more of a condition than the condition
 * says would show here as an arm proved shut that a row went through.
 *
 * <p>What it does not establish is the other half. An arm no row ran through is not shown
 * unreachable by that, and nothing here asks whether a proof that held over these rows holds over
 * every input.
 */
@ClosedWorldContract
class NoArmARowRanThroughIsOneProvedUnreachableTest {

    @Test
    void noRowRanThroughAnArmProvedShut() {
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
                for (var each : arrived.entrySet()) {
                    read++;
                    if (!each.getValue().provedWrong().isEmpty()) {
                        wrong.add(corpus.name() + " " + module + "." + each.getKey() + ": "
                                + each.getValue().provedWrong());
                    }
                }
            }
        }
        assertTrue(read > 0, "the corpora's behaviors were read as run, so the census counted"
                + " something");
        assertEquals(List.of(), wrong, "a row ran through an arm this compiler proved nothing"
                + " arrives at, so the proof is wrong");
    }
}
