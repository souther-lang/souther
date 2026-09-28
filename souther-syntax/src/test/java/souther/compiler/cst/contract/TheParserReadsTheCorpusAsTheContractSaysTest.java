package souther.compiler.cst.contract;

import souther.compiler.cst.CstParser;
import souther.test.CheckedInObservation;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code CstParser} reads every source of {@code syntax/corpus} the way the corpus says it is.
 *
 * <p>A case the corpus accepts is parsed with no error, and its tree, read as the contract tree,
 * is the one the case writes. A case marked {@code :error} is parsed with an error, and nothing
 * more is asked of it: where a reading stops and what it recovers is this parser's own and no
 * other implementation's business.
 *
 * <p>Accepting is not enough for a case that writes a tree. The rules the grammar states beyond
 * plain EBNF — a line break before an argument list, which match a {@code |} belongs to, what a
 * {@code with} value ends at — are mostly about which of two readings a source is, and both
 * readings parse; only the tree tells them apart.
 */
@CheckedInObservation
class TheParserReadsTheCorpusAsTheContractSaysTest {

    @Test
    void everyCaseIsReadAsItsTreeOrRefused() {
        List<String> wrong = new ArrayList<>();
        for (SyntaxCorpus.Case each : SyntaxCorpus.cases()) {
            CstParser.Result parsed = CstParser.parse(each.source());
            switch (each.expected()) {
                case SyntaxCorpus.Accepted accepted -> {
                    if (!parsed.errors().isEmpty()) {
                        wrong.add(each + "\n  is refused: " + parsed.errors());
                        continue;
                    }
                    ContractTree read = ContractProjection.of(parsed.root());
                    if (!read.equals(accepted.tree())) {
                        wrong.add(each + "\n  expected\n" + accepted.tree() + "\n  read\n" + read);
                    }
                }
                case SyntaxCorpus.Refused _ -> {
                    if (parsed.errors().isEmpty()) {
                        wrong.add(each + "\n  is accepted, and the corpus refuses it");
                    }
                }
            }
        }
        assertEquals("", String.join("\n\n", wrong));
    }
}
