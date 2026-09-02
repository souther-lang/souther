package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Derived;
import souther.compiler.check.Registry;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the derivation answered for is handed on as what it answered for.
 *
 * <p>One declaration may be read for what resolution left of it — its fields, what it includes,
 * whether it is a newtype, all of which mean the same thing whichever stage is asking. A whole table
 * may not. Turned back into nodes, every declaration below the stage arrives with nothing left
 * saying it came out, and a reader that needed the boundary representation is holding a declaration
 * that cannot tell it there is none.
 *
 * <p>The two halves are held apart here: the table the compilation's declarations are read through
 * says which stage they are at, and nothing carries a table across.
 */
class ATableOfDerivedDeclarationsIsNeverReadBackAsNodesTest {

    /** The registry a reader below the derivation is answered from hands over derived
     *  declarations. */
    @Test
    void theDerivedRegistryHandsOverDerivedDeclarations() throws NoSuchMethodException {
        Method registry = Names.class.getDeclaredMethod("derivedRegistry", Db.class);

        assertEquals(Registry.class, registry.getReturnType());
        assertEquals(List.of(Derived.Def.class), heldBy(registry.getGenericReturnType()),
                "the derived registry answers with something other than a derived declaration");
    }

    /** And the resolved one with declarations as resolution left them, which is the other world and
     *  not a projection of this one. */
    @Test
    void theResolvedRegistryHandsOverNodes() throws NoSuchMethodException {
        Method registry = Names.class.getDeclaredMethod("resolvedRegistry", Db.class);

        assertEquals(List.of(Hir.Def.class), heldBy(registry.getGenericReturnType()));
    }

    /**
     * Nothing anywhere turns a table of derived declarations into a table of nodes.
     *
     * <p>Read of the signatures rather than of what a body does, because the shape is what a later
     * change reaches for: a method handed the derived declarations and answering with the nodes is
     * how the stage came to be thrown away the first time, and it reads as a convenience until
     * somebody asks what the reader on the far side of it is holding.
     */
    @Test
    void nothingCarriesATableOfThemAcross() {
        List<String> carrying = new ArrayList<>();
        for (Class<?> each : List.of(Names.class, Shapes.class, Derived.class,
                souther.compiler.check.DerivedSymbols.class,
                souther.compiler.check.Declarations.class)) {
            for (Method m : each.getDeclaredMethods()) {
                boolean takesDerived = false;
                for (Type parameter : m.getGenericParameterTypes()) {
                    takesDerived |= heldBy(parameter).contains(Derived.Def.class);
                }
                if (takesDerived && heldBy(m.getGenericReturnType()).contains(Hir.Def.class)) {
                    carrying.add(each.getSimpleName() + "." + m.getName());
                }
            }
        }
        assertEquals(List.of(), carrying,
                "a table of derived declarations is read back as a table of nodes");
    }

    /**
     * A declaration nobody could derive is one no reader is told is settled.
     *
     * <p>The direction that holds, measured over a compile of the suite rather than argued: a
     * declaration that did not come out has no definition to name. The other way round does not
     * hold — a declaration comes out while the module around it has names that answer nothing — so
     * this is not a gate the derivation could be replaced by, and it is what a reader that filters
     * on one and reads through the other rests on.
     */
    @Test
    void aDeclarationThatDidNotComeOutIsNotSettledEither() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module probe.holes exposing ( Bad, Good )

                data Bad = { value: Nowhere }
                data Good = { n: Int }
                """), ModulePath.EMPTY);
        Db db = compilation.db();

        TypeKey bad = new TypeKey("probe.holes", "Bad");
        TypeKey good = new TypeKey("probe.holes", "Good");

        assertFalse(db.ask(new Shapes.DerivedDef(bad)).present(),
                "`Bad` holds a field naming nothing, so nothing derived it");
        assertFalse(db.ask(new Names.Definition(bad)).present(),
                "and nothing says it is settled either");
        assertTrue(db.ask(new Shapes.DerivedDef(good)).present(),
                "`Good` came out");
        assertTrue(db.ask(new Names.Definition(good)).present(),
                "and is settled");
    }

    /** What a type holds, as the classes named in its arguments. */
    private static List<Class<?>> heldBy(Type type) {
        List<Class<?>> out = new ArrayList<>();
        if (type instanceof ParameterizedType parameterized) {
            for (Type argument : parameterized.getActualTypeArguments()) {
                if (argument instanceof Class<?> named) {
                    out.add(named);
                } else {
                    out.addAll(heldBy(argument));
                }
            }
        }
        return out;
    }
}
