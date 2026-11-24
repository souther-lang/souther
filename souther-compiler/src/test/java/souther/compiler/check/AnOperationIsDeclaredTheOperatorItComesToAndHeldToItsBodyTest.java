package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation is the operator over two values of its type is declared of it, proved of the
 * body where the library writes it, and what a reader asks to know which operation an operator is
 * for the type it is written over — and whether an operation is one.
 */
class AnOperationIsDeclaredTheOperatorItComesToAndHeldToItsBodyTest {

    private static final ValueName STRING_APPEND = ValueName.Stdlib.operation("String", "append");
    private static final ValueName LIST_APPEND = ValueName.Stdlib.operation("List", "append");

    private static final String SHIPPED_LIST_APPEND =
            "let append (a: List<'a>, b: List<'a>): List<'a> = a ++ b";

    /** Control: the library as shipped, and which operation the operator is for each type. */
    @Test
    void theOperatorIsTheOperationOfTheTypeItIsWrittenOver() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertEquals(BinOp.CONCAT, facts.operatorOf(STRING_APPEND));
        assertEquals(BinOp.CONCAT, facts.operatorOf(LIST_APPEND));
        assertEquals(STRING_APPEND, facts.operationFor(BinOp.CONCAT, Type.STRING));
        assertEquals(LIST_APPEND, facts.operationFor(BinOp.CONCAT, new Type.ListOf(Type.INT)));
        assertNull(facts.operationFor(BinOp.CONCAT, Type.INT), "no operation is it over a number");
        assertNull(facts.operatorOf(ValueName.Stdlib.operation("List", "length")));
    }

    /** A written operation is the operator only where its body answers it on every run. */
    @Test
    void aBodyPuttingTheTwoTheOtherWayRoundIsNoOperator() {
        BoundOperationFacts facts = proved("let append (a: List<'a>, b: List<'a>): List<'a> = b ++ a");

        assertNull(facts.operatorOf(LIST_APPEND));
        assertTrue(facts.notProvedOfTheirBodies().stream().anyMatch(
                each -> each instanceof BoundOperationFact.IsTheOperator
                        && each.operation().operation().equals(LIST_APPEND)),
                "stated, and left unproved");
    }

    /** Two values of one type in and one of it out is an operator; anything else is refused. */
    @Test
    void anOperationNotTakingTwoOfOneTypeIsRefusedAsAnOperator() {
        IllegalStateException e = assertThrows(IllegalStateException.class, () -> {
            List<OperationFacts.Declared> declared =
                    new ArrayList<>(OperationFacts.declarations());
            declared.add(new OperationFacts.Declared(ValueName.Stdlib.operation("List", "length"),
                    new OperationFact.IsTheOperator(BinOp.CONCAT)));
            OperationFactBinder.bindAll(DefaultStdlib.get(), declared);
        });
        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** The library with {@code List.append} written as {@code body}, what is an operator proved. */
    private static BoundOperationFacts proved(String body) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(SHIPPED_LIST_APPEND)
                ? text.replace(SHIPPED_LIST_APPEND, body) : text);
        return OperationFactBinder.bindAll(stdlib, OperationFacts.declarations().stream()
                .filter(each -> each.fact() instanceof OperationFact.IsTheOperator)
                .toList());
    }
}
