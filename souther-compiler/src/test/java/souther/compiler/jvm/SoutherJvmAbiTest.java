package souther.compiler.jvm;

import org.junit.jupiter.api.Test;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What every class this compiler invents is called. The one place a generated class's name is written
 * out, and the only test that may.
 *
 * <p>Everything else — the compiler, and the tests that load what it emitted — asks
 * {@link SoutherJvmAbi}. That leaves nothing holding the ABI to its spellings, which is what this is
 * for: the names below are the specification, written independently of the mapping that produces
 * them, so a change to either shows up as a disagreement here. Spelled out at every reader instead,
 * one deliberate change to a name arrives as a few hundred failures, none of which says what changed.
 *
 * <p>Every branch of the mapping has a row, so a spelling cannot be changed without a row saying so.
 */
class SoutherJvmAbiTest {

    private static final TypeName ORDER = TypeSymbols.declared(new TypeKey("shop", "Order"));

    /** The specification, as a table: an identity and what it is called. */
    private static List<Object[]> abi() {
        List<Object[]> rows = new ArrayList<>();
        GeneratedClass.Value order = new GeneratedClass.Value(ORDER);

        // A declared type is its own name, in the module that declares it.
        rows.add(new Object[] {order, "shop.Order"});

        // A behavior's first letter is capitalized; the behavior's own name is not.
        rows.add(new Object[] {new GeneratedClass.BehaviorInterface("shop", "findOrder"),
                "shop.FindOrder"});
        rows.add(new Object[] {new GeneratedClass.BehaviorImpl("shop", "findOrder"),
                "shop.FindOrder$Impl"});
        rows.add(new Object[] {new GeneratedClass.BehaviorResult("shop", "findOrder"),
                "shop.FindOrderResult"});

        // A name with no upper-case form is emitted as it was written.
        rows.add(new Object[] {new GeneratedClass.BehaviorImpl("在庫", "引き当てる"),
                "在庫.引き当てる$Impl"});

        // A bridge case belongs to the module that emits it, not to the member's own module.
        rows.add(new Object[] {new GeneratedClass.BridgeCase("ship", TypeSymbols.declared(new TypeKey("inv", "Shortage"))),
                "ship.ShortageCase"});
        rows.add(new Object[] {new GeneratedClass.BridgeCase("m", TypeName.primitive("Int")),
                "m.IntCase"});

        // A codec sits beside what it encodes, whatever that is — a declared type or a union the
        // compiler generated.
        rows.add(new Object[] {new GeneratedClass.Encoder(order), "shop.Order$Enc"});
        rows.add(new Object[] {new GeneratedClass.Decoder(order, DecoderKind.VALUE), "shop.Order$Dec"});
        rows.add(new Object[] {new GeneratedClass.Decoder(order, DecoderKind.JSON), "shop.Order$DecJson"});
        rows.add(new Object[] {new GeneratedClass.Decoder(order, DecoderKind.RECORD), "shop.Order$DecRecord"});
        rows.add(new Object[] {new GeneratedClass.Encoder(
                new GeneratedClass.BehaviorResult("shop", "findOrder")), "shop.FindOrderResult$Enc"});

        rows.add(new Object[] {new GeneratedClass.Ctfe(order), "shop.Order$Ctfe"});
        rows.add(new Object[] {new GeneratedClass.ExampleFake(
                new GeneratedClass.BehaviorInterface("shop", "findOrder")), "shop.FindOrder$Fake"});

        // What belongs to a module rather than to anything in it.
        rows.add(new Object[] {new GeneratedClass.ModuleDeclarations("shop"), "shop.$Module"});
        rows.add(new Object[] {new GeneratedClass.Helpers("shop"), "shop.$Fns"});
        rows.add(new Object[] {new GeneratedClass.Lambda("shop", 0), "shop.$Fn0"});
        rows.add(new Object[] {new GeneratedClass.Lambda("shop", 7), "shop.$Fn7"});
        return rows;
    }

    @Test
    void everyGeneratedClassIsCalledWhatTheAbiSaysItIs() {
        for (Object[] row : abi()) {
            GeneratedClass generated = (GeneratedClass) row[0];
            assertEquals(row[1], SoutherJvmAbi.nameOf(generated).binaryName(), generated.toString());
        }
    }

    /** Every kind has at least one row. A kind added without one would be a spelling nothing here
     *  states, which is the state this test exists to make impossible. */
    @Test
    void andEveryKindOfGeneratedClassHasARow() {
        List<Class<?>> stated = new ArrayList<>();
        for (Object[] row : abi()) {
            Class<?> kind = row[0].getClass();
            if (!stated.contains(kind)) {
                stated.add(kind);
            }
        }
        List<Class<?>> kinds = NoPublicWayToMakeAGeneratedClassNameTest.kindsOf(GeneratedClass.class);
        List<Class<?>> missing = new ArrayList<>(kinds);
        missing.removeAll(stated);
        assertEquals(List.of(), missing, "a kind of generated class with no name written down");
        assertEquals(kinds.size(), stated.size());
    }

    /** Where a class of a given name is written, which is the JVM's rule and is stated here for the
     *  same reason the rest is: four readers wanted it and each wrote it out. */
    @Test
    void andAClassOfThatNameIsWrittenWhereTheAbiSaysItIs() {
        assertEquals("shop/Order.class", JvmClassName.classFile("shop.Order"));
        assertEquals("shop/FindOrder$Impl.class",
                SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorImpl("shop", "findOrder")).classFile());
        assertEquals("在庫/引き当てる$Impl.class",
                SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorImpl("在庫", "引き当てる")).classFile());
        assertEquals("Loose.class", JvmClassName.classFile("Loose"));
    }

    /**
     * The one naming rule that runs backwards, and the half of the question it answers.
     *
     * <p>A value class is its type, so the two directions are one rule and it is written once. What
     * comes back is the type whose value class <em>would</em> be spelled that way — nothing more.
     * Whether such a type is declared is a scope's answer, and so is what was really emitted under
     * the name: {@code shop.FindOrder$Impl} is not a declaration any source could write, and
     * {@code souther.Int} is a primitive, which reaches codegen as a boxed class and never as a value
     * class of its own. Both read back here all the same, because reading back is all this does.
     */
    @Test
    void andAValueClassNameSaysWhichTypeItWouldBe() {
        for (TypeName type : List.of(ORDER, TypeSymbols.declared(new TypeKey("在庫", "金額")),
                TypeSymbols.declared(new TypeKey("a.b.c", "Deep")), TypeName.primitive("Int"))) {
            assertEquals(type, SoutherJvmAbi.valueTypeCandidate(
                    SoutherJvmAbi.nameOf(new GeneratedClass.Value(type)).binaryName()));
        }
        assertEquals(TypeSymbols.declared(new TypeKey("shop", "FindOrder$Impl")),
                SoutherJvmAbi.valueTypeCandidate("shop.FindOrder$Impl"),
                "a candidate for the name, and no claim about what is under it");
        assertEquals(null, SoutherJvmAbi.valueTypeCandidate("Loose"), "a name with no module names no type");
        assertEquals(null, SoutherJvmAbi.valueTypeCandidate(".Foo"));
        assertEquals(null, SoutherJvmAbi.valueTypeCandidate("demo."));
    }

    /** And every decoder does, which is the one branch that is a value rather than a kind. */
    @Test
    void andEveryDecoderHasARow() {
        List<DecoderKind> stated = new ArrayList<>();
        for (Object[] row : abi()) {
            if (row[0] instanceof GeneratedClass.Decoder d && !stated.contains(d.kind())) {
                stated.add(d.kind());
            }
        }
        assertEquals(List.of(DecoderKind.values()).size(), stated.size(),
                "a decoder kind with no name written down: " + stated);
    }
}
