package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A kept call refuses its function argument where the argument is written.
 *
 * <p>Both kinds of argument are held to the signature in one method, and they are one rule: a value
 * given to a position it does not fit. A value argument is refused at its own region and a function
 * argument was refused at the callee, because the check the second one goes through is handed two
 * types and the call's position rather than the argument. The path a reader reaches this on is the
 * discharge representation, where the language's own operations are kept standing.
 */
class AKeptCallsFunctionArgumentIsRefusedWhereItIsWrittenTest {

    private static final SourcePos CALL = new SourcePos(1, 1);
    private static final SourcePos ARGUMENT = new SourcePos(3, 5);

    /**
     * {@code List.flatMap : (('a) -> List<'b>, List<'a>) -> List<'b>} — the function argument is
     * declared to answer a list, and this one answers an Int. The block is written two lines below
     * the callee, so only the block's own position puts the caret on a line the reader has to look
     * at.
     */
    @Test
    void aBlockThatAnswersTheWrongTypeIsUnderlinedWhereItIsWritten() {
        Ast.Binders binders = new Ast.Binders(new BindingOwner.OfValue("demo", "test"));
        Ast.Block answersAnInt = new Ast.Block(List.of(binders.binder("x", ARGUMENT)),
                new Ast.IntLit(1, ARGUMENT, null), ARGUMENT, null);
        Ast.Expr call = new Ast.Apply("List.flatMap", new ValueName.Stdlib("List", "flatMap"),
                new ReachName.OfLibrary(new ValueName.Stdlib("List", "flatMap")),
                List.of(answersAnInt, new Ast.ListLit(List.of(new Ast.IntLit(2, CALL, null)), CALL, null)),
                ConstructionOrigin.own(), CALL, null);

        CompileException e = assertThrows(CompileException.class,
                () -> Elaborator.elaborate(call, Scope.NONE, CheckContext.of(Symbols.none())
                        .preserving(Preserved.byTheLanguagesOwnOperations())));

        assertEquals(ARGUMENT.line(), e.diagnostic().region().start().line(),
                "the block is on line " + ARGUMENT.line() + " and the callee on line "
                        + CALL.line());
    }

    /**
     * And it is refused by the sentence a value argument is refused by. Which of two sentences a
     * reader gets is not something a reader can see, so one rule states itself one way.
     */
    @Test
    void itIsRefusedBySameSentenceAsAValueArgument() {
        Ast.Binders binders = new Ast.Binders(new BindingOwner.OfValue("demo", "test"));
        Ast.Block answersAnInt = new Ast.Block(List.of(binders.binder("x", ARGUMENT)),
                new Ast.IntLit(1, ARGUMENT, null), ARGUMENT, null);
        Ast.Expr call = new Ast.Apply("List.flatMap", new ValueName.Stdlib("List", "flatMap"),
                new ReachName.OfLibrary(new ValueName.Stdlib("List", "flatMap")),
                List.of(answersAnInt, new Ast.ListLit(List.of(new Ast.IntLit(2, CALL, null)), CALL, null)),
                ConstructionOrigin.own(), CALL, null);

        CompileException e = assertThrows(CompileException.class,
                () -> Elaborator.elaborate(call, Scope.NONE, CheckContext.of(Symbols.none())
                        .preserving(Preserved.byTheLanguagesOwnOperations())));

        TypeMessage.ItDoesNotHaveTheTypeItNeedsHere said = assertInstanceOf(
                TypeMessage.ItDoesNotHaveTheTypeItNeedsHere.class, e.diagnostic().said());
        assertEquals("argument 1 of List.flatMap", said.what());
    }
}
