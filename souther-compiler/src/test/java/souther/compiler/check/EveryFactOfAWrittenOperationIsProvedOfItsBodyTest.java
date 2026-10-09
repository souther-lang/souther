package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is stated of an operation the library writes in the language is a fact only where its body
 * proves it, and one it does not prove is an obligation no reader takes. So a statement left
 * unproved is a fact the checks lose without a word, and the library is held here to having none:
 * every law, closing, bound and case stated of a written operation is proved of its body, and so is
 * everything stated of what it builds — where its elements came from and in what order, which keys
 * it keeps, what it is no smaller than, what its truth survives and is stated over.
 */
class EveryFactOfAWrittenOperationIsProvedOfItsBodyTest {

    @Test
    void nothingStatedOfAWrittenOperationIsLeftUnproved() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        List<String> open = new ArrayList<>();
        facts.settled().forEach((operation, of) -> of.forEach((observed, settling) -> {
            if (settling instanceof BoundOperationFacts.Settled.Open(var _, var why)) {
                open.add(operation + " " + observed + ": " + why);
            }
        }));
        facts.notProvedOfTheirBodies().forEach(each -> open.add(each.toString()));
        assertEquals(List.of(), open,
                "a statement of a written operation its body does not prove");
    }
}
