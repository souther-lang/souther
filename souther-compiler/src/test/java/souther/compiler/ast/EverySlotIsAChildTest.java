package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ConstructionOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What the two walks over an expression reach, and which operator each slot goes through.
 *
 * <p>A name is a name wherever it stands, so a spread is a child and a pass that asks what an
 * expression names finds one without knowing that spreads exist. Which slot it stands in decides
 * only what may replace it: an expression slot takes any expression, a name slot takes a name.
 *
 * <p>These are here rather than left to the passes that depend on them because the walk is what
 * every pass delegates to: a slot missing from it is missing from all of them at once, and nothing
 * in a pass says which slots there were supposed to be.
 */
class EverySlotIsAChildTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Ast.Var name(String written) {
        return new Ast.Var(written, POS);
    }

    /** {@code Person { ..base, age: n }} — one name slot, one expression slot. */
    private static Ast.NewData construction() {
        return new Ast.NewData(Ast.Name.written("Person", POS),
                List.of(new Ast.FieldInit("age", name("n"), POS)),
                List.of(name("base")),
                ConstructionOrigin.own(), POS);
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

    @Test
    void aSpreadGoesThroughTheNameOperatorAndAFieldValueThroughTheExpressionOperator() {
        List<String> asExpressions = new ArrayList<>();
        List<String> asNames = new ArrayList<>();

        Ast.mapChildren(construction(), child -> {
            asExpressions.add(child.toString());
            return child;
        }, spread -> {
            asNames.add(spread.name());
            return spread;
        });

        assertEquals(List.of("n"), asExpressions);
        assertEquals(List.of("base"), asNames);
    }

    /** The name operator answers a {@code Var}, so a rewrite has nothing else it could put there. */
    @Test
    void aRewriteOfANameSlotIsANameAgain() {
        Ast.NewData rewritten = (Ast.NewData) Ast.mapChildren(construction(),
                child -> child, spread -> name("other"));

        assertEquals(List.of("other"), rewritten.spreads().stream().map(Ast.Var::name).toList());
    }

    /** A read-only walk allocates nothing: every slot answered what it was given, so the node it
     * walked is the node it returns. */
    @Test
    void aWalkThatChangesNothingKeepsTheNodeItWalked() {
        Ast.NewData built = construction();

        assertSame(built, Ast.mapChildren(built, child -> child, spread -> spread));
    }
}
