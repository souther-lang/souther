package souther.compiler;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A spread names a value the same way any other position does. An {@code example} row and a behavior
 * body are the same language here: a record written with {@code ...base} in a row and the same record
 * written in a body must both reach the value {@code base} stands for.
 */
class CompileValueSpreadTest {

    private BytesClassLoader loader(String source) {
        return new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
    }

    private static Object aged(BytesClassLoader loader) throws Exception {
        Object behavior = Emitted.behavior(loader, "demo", "go").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", 1L)));
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Person", out)).get("age");
    }

    @Test
    void aRecordValueMayBeSpreadInOrdinaryCode() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }

                let base = Person { name = "A", age = 20 }

                behavior go : (i: In) -> Person constructs Person
                let go (i) = Person { ...base, age = 21 }
                """);

        assertEquals(21L, aged(loader));
    }

    @Test
    void aChainOfRecordValuesMayBeSpread() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }

                let origin = Person { name = "A", age = 20 }
                let base = Person { ...origin, name = "B" }

                behavior go : (i: In) -> Person constructs Person
                let go (i) = Person { ...base, age = 22 }
                """);

        assertEquals(22L, aged(loader));
    }

    /** A binding in force wins over a declaration, in a spread as anywhere else. */
    @Test
    void aParameterSpreadShadowsASameNamedTopLevelValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Person = { name: String, age: Int }

                let base = Person { name = "global", age = 10 }

                behavior update : (base: Person) -> Person constructs Person
                let update (base) = Person { ...base, age = 20 }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "update").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.Person", Map.of("name", "argument", "age", 1L));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Person",
                Codecs.apply(behavior, in));

        assertEquals("argument", out.get("name"));
    }

    @Test
    void aLocalSpreadShadowsASameNamedTopLevelValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { name: String }
                data Person = { name: String, age: Int }

                let base = Person { name = "global", age = 10 }

                behavior update : (i: In) -> Person constructs Person
                let update (i) = {
                    let base = Person { name = i.name, age = 1 }
                    Person { ...base, age = 20 }
                }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "update").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("name", "local"));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Person",
                Codecs.apply(behavior, in));

        assertEquals("local", out.get("name"));
    }

    /**
     * A published value is substituted where it is named, so the reader needs its body — and the
     * bodies that body needs. A spread names one of those the way a bare name does, so the value it
     * spreads travels with it.
     */
    @Test
    void aPublishedValueCarriesTheValueItSpreads() {
        ModulePath library = ModulePath.of(Compiler.compile("""
                module shared.people exposing ( Person, listed )

                data Person = { name: String, age: Int }

                let base = Person { name = "A", age = 20 }
                let listed = Person { ...base, age = 21 }
                """));

        assertDoesNotThrow(() -> Compiler.compileModules(java.util.List.of("""
                module app.roster exposing ( Entry )

                import shared.people ( Person, listed )

                data Entry = { of: Person }

                behavior enrol : (p: Person) -> Entry constructs Entry
                let enrol (p) = Entry { of = listed }
                """), library));
    }

    /** A spread names a value the way any other position does, so what that value built came in
     * with it. The spreading behavior copies fields out of something already made, and the `Person`
     * behind the spread is the value definition's. */
    @Test
    void aValueSpreadIsNotTheSpreadingBehaviorsConstruction() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }
                data Stamped = { name: String, age: Int }

                let base = Person { name = "A", age = 20 }

                behavior go : (i: In) -> Stamped constructs Stamped
                let go (i) = Stamped { ...base, age = 21 }
                """));
    }
}
