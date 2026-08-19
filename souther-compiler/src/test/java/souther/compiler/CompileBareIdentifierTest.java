package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A bare identifier is a local if one is bound, and otherwise the construction of the unit data
 * of that name (spec §unit-data). Souther does not distinguish the two by caseName — business vocabulary is
 * written in Japanese, which has none — so the scope decides.
 */
class CompileBareIdentifierTest {

    /** Regression: the permission check read a local as constructing the unit data it shadows. */
    @Test
    void aLocalShadowsAUnitDataOfTheSameName() {
        String src = """
                module demo
                data 立替
                data R = { v: Int }
                behavior f : (立替: Int) -> R constructs R
                let f (立替) = R { v = 立替 }
                """;
        assertTrue(Compiler.compile(src).containsKey("demo.F"), "立替 here is the parameter, not a construction");
    }

    @Test
    void aLetAlsoShadows() {
        String src = """
                module demo
                data 立替
                data R = { v: Int }
                behavior f : (x: Int) -> R constructs R
                let f (x) = {
                    let 立替 = x
                    R { v = 立替 }
                }
                """;
        assertTrue(Compiler.compile(src).containsKey("demo.F"));
    }

    /**
     * With nothing bound, the same name is the unit's construction — and needs no declaring.
     *
     * <p>A unit data is in no behavior's construction set (spec §constructs-excludes-unit-data), so
     * the bare name being a construction is not a thing the clause records. That leaves the class
     * file no help at all as a witness: {@code demo.立替} is emitted by the declaration whether or
     * not the body ever writes the name. So the behavior is run, and what proves the name was read
     * as the construction is the value each arm comes back with.
     */
    @Test
    void anUnboundNameConstructsTheUnitData() throws Exception {
        String src = """
                module demo
                data 立替
                data 空
                behavior f : (x: Int) -> 立替 | 空
                let f (x) = if x > 0 then 立替 else 空
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object f = Emitted.behavior(loader, "demo", "f").getConstructor().newInstance();

        assertEquals("demo.立替", Codecs.apply(f, 1L).getClass().getName());
        assertEquals("demo.空", Codecs.apply(f, 0L).getClass().getName());
    }

    /** And naming it in the clause is refused rather than accepted. */
    @Test
    void declaringItIsRefused() {
        String src = """
                module demo
                data 立替
                behavior f : (x: Int) -> 立替
                    constructs 立替
                let f (x) = 立替
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1026", e.code());
    }

    /** The unit is still built where the name is written, clause or no clause. */
    @Test
    void theUnitIsBuiltWithNoClauseAtAll() {
        String src = """
                module demo
                data 立替
                behavior f : (x: Int) -> 立替
                let f (x) = 立替
                """;
        assertTrue(Compiler.compile(src).containsKey("demo.F"));
    }
}
