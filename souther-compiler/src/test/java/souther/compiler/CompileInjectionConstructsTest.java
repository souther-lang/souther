package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * An injected behavior (a signature with no fn — spec §injected-behavior) hands its Java implementation a
 * {@code protected} factory for every declared unit-data case, and nothing else. A non-unit case
 * it declares in {@code constructs} must therefore be reachable another way: as an exposed data
 * whose {@code decoder} is public (spec §java-base-class). One that is neither a unit nor exposed cannot be
 * built by the Java side at all — E1305. A unit case needs no exposure; {@link CompileBehaviorResultTest}
 * compiles an injected behavior answering an unexposed unit.
 */
class CompileInjectionConstructsTest {

    @Test
    void anExposedNonUnitCaseIsAllowed() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo
                exposing ( Id, Member, 保存データ不正 )

                data Id = String
                data Member = { id: Id }
                data 保存データ不正 = { reason: String }

                behavior findMember : (id: Id) -> Member | 保存データ不正
                    constructs 保存データ不正
                """));
    }

    @Test
    void aNonUnitUnexposedCaseIsE1305() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ( Id, Member )

                data Id = String
                data Member = { id: Id }
                data 保存データ不正 = { reason: String }

                behavior findMember : (id: Id) -> Member | 保存データ不正
                    constructs 保存データ不正
                """));
        assertEquals("E1305", e.code());
    }

    /** A module with no clause publishes the case, so Java has its decoder. */
    @Test
    void aCaseOfAModuleWritingNoClauseIsAllowed() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Id = String
                data Member = { id: Id }
                data 保存データ不正 = { reason: String }

                behavior findMember : (id: Id) -> Member | 保存データ不正
                    constructs 保存データ不正
                """));
    }

    /** One writing {@code exposing ()} publishes nothing, the case included. */
    @Test
    void aCaseOfAModuleWritingAnEmptyClauseIsE1305() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                exposing ()

                data Id = String
                data Member = { id: Id }
                data 保存データ不正 = { reason: String }

                behavior findMember : (id: Id) -> Member | 保存データ不正
                    constructs 保存データ不正
                """));
        assertEquals("E1305", e.code());
    }
}
