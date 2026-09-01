package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the walk over an expression reaches, and in which order.
 *
 * <p>A name is a name wherever it stands, so a spread is a child and a pass that asks what an
 * expression names finds one without knowing that spreads exist.
 *
 * <p>This is here rather than left to the passes that depend on it because the walk is what every
 * pass delegates to: a slot missing from it is missing from all of them at once, and nothing in a
 * pass says which slots there were supposed to be.
 */
class EverySlotIsAChildTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Ast.Var name(String written) {
        return Ast.Var.written(written, POS);
    }

    /** {@code Person { ..base, age: n }} — one name slot, one expression slot. */
    private static Ast.NewData construction() {
        return new Ast.NewData(Ast.Name.written("Person", POS),
                List.of(new Ast.FieldInit(WrittenName.of("age", POS), name("n"))),
                List.of(name("base")),
                ConstructionOrigin.own(), POS, null);
    }

    private static List<Ast.Expr> childrenOf(Ast.Expr e) {
        List<Ast.Expr> out = new ArrayList<>();
        Ast.forEachChild(e, out::add);
        return out;
    }

    @Test
    void aSpreadIsAChild() {
        assertEquals(List.of("base", "n"),
                childrenOf(construction()).stream().map(Object::toString).toList(),
                "the spread and the field's value, in the order they are written");
    }
}
