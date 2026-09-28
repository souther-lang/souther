package souther.compiler.cst.contract;

import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The corpus's trees are written in the nodes the grammar names, and every one of those nodes is
 * written in some tree.
 *
 * <p>The first half keeps a tree from naming a node the grammar has not declared, which a typo in
 * either would otherwise do silently: the parser would be held to a tree no grammar describes. The
 * second half is what makes the corpus a witness of the grammar and not of a part of it. A node no
 * accepted case writes is one no implementation is held to, and the grammar's word for it is then
 * the only thing saying what it is.
 */
@ClosedWorldContract
class EveryNodeTheGrammarNamesIsWitnessedTest {

    @Test
    void theTreesAndTheGrammarNameTheSameNodes() {
        Set<String> written = new TreeSet<>();
        for (SyntaxCorpus.Case each : SyntaxCorpus.cases()) {
            if (each.expected() instanceof SyntaxCorpus.Accepted accepted) {
                List<String> ids = new ArrayList<>();
                accepted.tree().collectIds(ids);
                written.addAll(ids);
            }
        }
        assertEquals(new TreeSet<>(SyntaxContract.grammar().nodes()), written,
                "the nodes the grammar marks and the nodes the corpus writes");
    }
}
