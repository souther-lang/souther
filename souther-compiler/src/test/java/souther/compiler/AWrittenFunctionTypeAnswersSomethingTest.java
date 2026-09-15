package souther.compiler;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A function type in the resolved tree answers something, and a source that writes one which does
 * not is refused before the tree is built.
 *
 * <p>The two halves are one claim seen from each end. A written function type with no result is a
 * shape the grammar recovers to, so {@link souther.compiler.ast.Ast.FnType} holds it and a reading
 * of the text can say where it went wrong. Below the reading nothing may: a reader of a resolved
 * type walks its result, and an absence there is one every walk would have to carry a question
 * about — the same reason a reference that denotes nothing is not a state of the resolved tree.
 *
 * <p>So the refusal here is not a report to an author. It says the reading above let something
 * through, which is why it is asked of the constructor and not of a source. What keeps an author
 * from meeting it is the other half, and that is why both are here: a refusal whose premise nobody
 * holds is one a change upstream can turn into the answer an author gets.
 */
class AWrittenFunctionTypeAnswersSomethingTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    @Test
    void theResolvedTreeCannotHoldAFunctionTypeThatAnswersNothing() {
        assertThrows(IllegalArgumentException.class,
                () -> new Hir.FnType(List.of(), null, POS),
                "a function type with no result is a shape every reader below would have to ask"
                        + " about, so the tree does not hold one");
    }

    /** What it takes is walked the way what it answers is, so the rule is the same rule. */
    @Test
    void norOneThatTakesSomethingUnwritten() {
        List<Hir.RetType> unwritten = new ArrayList<>();
        unwritten.add(null);

        assertThrows(IllegalArgumentException.class,
                () -> new Hir.FnType(unwritten, answering(), POS),
                "a parameter that says nothing is the same absence a missing result is");
    }

    private static Hir.RetType answering() {
        return Hir.RetType.of(List.of(Hir.TypeRef.of(Type.BOOL, POS)), POS);
    }

    @Test
    void aFunctionTypeWrittenWithoutOneIsRefusedWhereItIsWritten() {
        for (String written : List.of("(Int)", "(Int) ->")) {
            CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                    module demo

                    behavior f : (n: Int) -> Int
                    let f (n) = let g (h: %s) = h(n) in g((x) -> x)
                    """.formatted(written)));

            assertInstanceOf(ParseMessage.class, refused.diagnostics().get(0).said(),
                    "`" + written + "` says no result, and what is wrong with it is the text");
        }
    }
}
