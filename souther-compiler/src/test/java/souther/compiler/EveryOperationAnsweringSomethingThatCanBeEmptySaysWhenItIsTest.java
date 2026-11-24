package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every library operation whose answer can be empty, or absent, either says when it is or says
 * why it cannot.
 *
 * <p>A reader that asks what makes a container hold something, or an option hold a value, takes it
 * from the operation that made it. Where the operation says nothing the reader gets no condition,
 * and everything resting on one — that a closure over the container is entered only where it holds
 * an entry, for one — goes unshown. So an operation added without its law narrows what is read,
 * and nothing says so; this is what does.
 */
class EveryOperationAnsweringSomethingThatCanBeEmptySaysWhenItIsTest {

    @Test
    void everyOperationAnsweringAContainerAStringOrAnOptionSettlesWhetherItHoldsSomething() {
        List<String> unsettled = new ArrayList<>();
        for (Map.Entry<ValueName.Stdlib.Operation, Stdlib.Entry> each
                : DefaultStdlib.get().entries().entrySet()) {
            Type result = each.getValue().signature().result();
            OperationLaw.Observed side;
            if (result instanceof Type.OptionOf) {
                side = OperationLaw.Observed.PRESENCE;
            } else if (Type.elementOfAContainer(result) != null || Type.STRING.equals(result)) {
                side = OperationLaw.Observed.EMPTINESS;
            } else {
                continue;
            }
            Map<OperationLaw.Observed, BoundOperationFacts.Settled> settled =
                    DefaultBoundOperationFacts.get().settled().get(each.getKey());
            BoundOperationFacts.Settled how = settled == null ? null : settled.get(side);
            if (!(how instanceof BoundOperationFacts.Settled.ByALaw
                    || how instanceof BoundOperationFacts.Settled.Unsaid)) {
                unsettled.add(each.getKey() + " " + side);
            }
        }
        assertEquals(List.of(), unsettled);
    }
}
