package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What each substitution replaces and what it leaves, at any depth. Which positions a compound
 * holds is {@link Type#mapChildren}'s to say, so these ask only the leaf rule and that a type with
 * nothing replaced comes back as the instance it was given.
 */
class TypeOpsSubstitutionTest {

    private static final Type A = Type.var("'a");
    private static final Type B = Type.var("'b");
    private static final Type.MetaVar META_A =
            new Type.MetaVar(new BindingOwner.OfValue("m", "f"), "'a");
    private static final Type.MetaVar META_OTHER =
            new Type.MetaVar(new BindingOwner.OfValue("m", "g"), "'a");

    private static Type nesting(Type leaf) {
        return Type.map(Type.STRING, Type.tuple(List.of(
                Type.list(leaf),
                Type.fn(List.of(Type.option(leaf)), Type.set(leaf)))));
    }

    @Test
    void aVariableInsideListMapTupleAndFunctionIsReplaced() {
        assertEquals(nesting(Type.INT), TypeOps.substitute(nesting(A), Map.of("'a", Type.INT)));
    }

    @Test
    void aVariableWithNoBindingIsLeftAsItIs() {
        assertEquals(nesting(B), TypeOps.substitute(nesting(B), Map.of("'a", Type.INT)));
    }

    @Test
    void aSubstitutionDoesNotFollowWhatItPutThere() {
        assertEquals(B, TypeOps.substitute(A, Map.of("'a", B, "'b", Type.INT)));
    }

    @Test
    void aMetaVariableInsideListMapTupleAndFunctionIsReplaced() {
        assertEquals(nesting(Type.INT),
                TypeOps.substituteMetas(nesting(META_A), Map.of(META_A, Type.INT)));
    }

    @Test
    void aMetaVariableOfAnotherApplicationIsLeftAsItIs() {
        assertEquals(nesting(META_OTHER),
                TypeOps.substituteMetas(nesting(META_OTHER), Map.of(META_A, Type.INT)));
    }

    @Test
    void eachSubstitutionLeavesTheOtherKindOfVariableAlone() {
        Type both = Type.tuple(List.of(A, META_A));
        assertEquals(Type.tuple(List.of(Type.INT, META_A)),
                TypeOps.substitute(both, Map.of("'a", Type.INT)));
        assertEquals(Type.tuple(List.of(A, Type.INT)),
                TypeOps.substituteMetas(both, Map.of(META_A, Type.INT)));
    }

    @Test
    void nothingReplacedIsTheInstanceGiven() {
        Type t = nesting(B);
        assertSame(t, TypeOps.substitute(t, Map.of("'a", Type.INT)));
        Type metas = nesting(META_OTHER);
        assertSame(metas, TypeOps.substituteMetas(metas, Map.of(META_A, Type.INT)));
    }

    @Test
    void aSiblingOfAReplacedPositionIsReused() {
        Type untouched = Type.option(Type.STRING);
        Type.TupleOf result = (Type.TupleOf) TypeOps.substitute(
                Type.tuple(List.of(untouched, Type.list(A))), Map.of("'a", Type.INT));
        assertSame(untouched, result.elements().get(0));
        assertEquals(Type.list(Type.INT), result.elements().get(1));
    }

    @Test
    void toBottomReadsAVariableInsideAFunctionAndATupleAsTheBottom() {
        assertEquals(
                Type.tuple(List.of(Type.fn(List.of(Type.NOTHING), Type.list(Type.NOTHING)),
                        Type.map(Type.STRING, Type.NOTHING))),
                TypeOps.toBottom(Type.tuple(List.of(Type.fn(List.of(A), Type.list(A)),
                        Type.map(Type.STRING, B)))));
    }

    @Test
    void toBottomLeavesAMetaVariableAlone() {
        Type t = Type.list(META_A);
        assertSame(t, TypeOps.toBottom(t));
    }
}
