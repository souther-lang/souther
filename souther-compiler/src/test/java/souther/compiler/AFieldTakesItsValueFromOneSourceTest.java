package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Where more than one spread carries a field, the first of them supplies it, and that is the whole
 * of the rule — the value that reaches the field at run time, the type the field is checked
 * against, and what the construction is read as all name the same source.
 *
 * <p>This is held because the two used to disagree. What ran took the first spread carrying the
 * field; what was type-checked took the last, since the fields each spread supplies were collected
 * into one map. A construction now resolves each field once, where it is elaborated, so there is one
 * winner for a reader to see. The rule follows what already ran; the spec says only that a spread
 * copies the fields of one value and that surplus ones are ignored (§record-literal), so what
 * several spreads do about one field is written down there rather than derived from here.
 */
class AFieldTakesItsValueFromOneSourceTest {

    private static final String MODULE = """
            module demo

            data From = { n: Int, tag: String }
            data Also = { n: Int, other: Int }
            data Odd  = { n: String, other: Int }

            data T = { n: Int, tag: String }

            data In = { from: From, also: Also }

            behavior pick : (i: In) -> T
                constructs T

            let pick (i) = %s
            """;

    private Map<?, ?> run(String body) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compile(MODULE.formatted(body)), getClass().getClassLoader());
        Map<String, Object> from = new HashMap<>();
        from.put("n", 1);
        from.put("tag", "first");
        Map<String, Object> also = new HashMap<>();
        also.put("n", 2);
        also.put("other", 9);
        Map<String, Object> in = new HashMap<>();
        in.put("from", from);
        in.put("also", also);
        Object value = Codecs.decoded(loader, "demo.In", in);
        Object behavior = Emitted.behavior(loader, "demo", "pick").getConstructor().newInstance();
        return (Map<?, ?>) Codecs.encode(loader, "demo.T", Codecs.apply(behavior, value));
    }

    @Test
    void theFirstSpreadCarryingTheFieldSuppliesIt() throws Exception {
        assertEquals(1L, run("T { ...i.from, ...i.also }").get("n"));
        assertEquals(2L, run("T { ...i.also, ...i.from }").get("n"));
    }

    @Test
    void aFieldWrittenOutBeatsEverySpread() throws Exception {
        assertEquals(7L, run("T { ...i.from, ...i.also, n = 7 }").get("n"));
    }

    /**
     * The field is checked against the type of the spread that supplies it. A later spread carrying
     * the same name carries it no more than any other surplus field it has.
     *
     * <p>This program was refused (E1016) while the two answers differed: the type came from the
     * last spread carrying the field and the value from the first, so a field the first supplied
     * correctly was refused for the second's type — a type error about a value that was never going
     * to be read.
     */
    @Test
    void aLaterSpreadsFieldOfAnotherTypeIsSurplus() {
        Compiler.compile("""
                module demo

                data From = { n: Int, tag: String }
                data Odd  = { n: String, other: Int }
                data T = { n: Int, tag: String }
                data In = { from: From, also: Odd }

                behavior pick : (i: In) -> T
                    constructs T

                let pick (i) = T { ...i.from, ...i.also }
                """);
    }

    /** The same program with the sources the other way round is refused, which is what says the
     * first spread is the one being read rather than that neither is. */
    @Test
    void theFirstSpreadsFieldOfAnotherTypeIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data From = { n: Int, tag: String }
                data Odd  = { n: String, other: Int }
                data T = { n: Int, tag: String }
                data In = { from: From, also: Odd }

                behavior pick : (i: In) -> T
                    constructs T

                let pick (i) = T { ...i.also, ...i.from }
                """));

        assertEquals("E1016", refused.diagnostics().get(0).code());
    }
}
