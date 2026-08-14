package souther.compiler.types;

import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeKey;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code Type.mentions} walks every type nested inside a type: what a collection holds, what a
 * tuple carries, and what a function type takes and answers. A name a {@code Union} lists is not
 * a nested type — its members are names, not types — so the walk ends there.
 */
class TypeMentionsTest {

    private static boolean isVar(Type t) {
        return t instanceof Type.Var;
    }

    @Test
    void aFunctionResultIsWalked() {
        Type fn = Type.fn(List.of(Type.INT), Type.var("'a"));
        assertTrue(Type.mentions(fn, TypeMentionsTest::isVar));
    }

    @Test
    void aFunctionParameterIsWalked() {
        Type fn = Type.fn(List.of(Type.var("'a")), Type.INT);
        assertTrue(Type.mentions(fn, TypeMentionsTest::isVar));
    }

    @Test
    void aFunctionInsideATupleIsWalked() {
        Type carried = Type.tuple(List.of(Type.INT, Type.fn(List.of(Type.INT), Type.var("'a"))));
        assertTrue(Type.mentions(carried, TypeMentionsTest::isVar));
    }

    @Test
    void aUnionMemberIsANameNotANestedType() {
        Type union = Type.union(Set.of(TypeSymbols.declared(new TypeKey("m", "A")), TypeSymbols.declared(new TypeKey("m", "B"))));
        assertFalse(Type.mentions(union, t -> t instanceof Type.Ref));
    }

    @Test
    void aCollectionElementIsWalked() {
        assertTrue(Type.mentions(Type.list(Type.var("'a")), TypeMentionsTest::isVar));
        assertTrue(Type.mentions(Type.map(Type.STRING, Type.var("'a")), TypeMentionsTest::isVar));
        assertFalse(Type.mentions(Type.list(Type.INT), TypeMentionsTest::isVar));
    }
}
