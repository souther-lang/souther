package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A composition another project compiled is a composition here, and is refused where one compiled
 * beside this module is.
 *
 * <p>A jar carries a composition as the signature its stages compute, written out as source, and
 * source has no way to say that signature was not declared. Read back as a declaration, the
 * composition was a behavior like any other: a body could call it by name, and {@code depends on}
 * it was told to call it directly instead. Each case below is asked twice — once with the
 * publishing module compiled beside the reader, once with it read off the path — and the two are
 * held to the same answer, so what is compared is where the module came from and nothing else.
 */
class ACompositionFromAJarIsStillACompositionTest {

    private static final String PUBLISHED = """
            module lib.rates exposing ( rate, double, priced : Int )

            behavior rate : (n: Int) -> Int

            behavior double : (n: Int) -> Int
            let double (n) = n + n

            behavior priced = rate >-> double
            """;

    /** The jar, built once for every case: what a reader is compiled against is its classes, and
     *  nothing a reader does changes them. */
    private static final ModulePath JAR = ModulePath.of(Compiler.compile(PUBLISHED));

    @Test
    void aBodyCannotCallOneByName() {
        assertSameRefusal("""
                module app.uses
                import lib.rates ( priced )

                behavior useIt : (n: Int) -> Int
                let useIt (n) = priced(n)
                """, "E1818");
    }

    @Test
    void aDependsOnCannotRestOnOne() {
        assertSameRefusal("""
                module app.uses
                import lib.rates ( priced )

                behavior useIt : (n: Int) -> Int
                    depends on priced
                let useIt (n, priced) = priced(n)
                """, "E1607");
    }

    /** {@code reader} is refused with {@code code} for the same reason whichever way the module it
     *  imports arrives. */
    private static void assertSameRefusal(String reader, String code) {
        Diagnostic together = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(PUBLISHED, reader))).diagnostic();
        Diagnostic offThePath = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(reader), JAR)).diagnostic();

        assertEquals(code, together.code());
        assertEquals(together.code(), offThePath.code());
        assertEquals(together.said().getClass(), offThePath.said().getClass(),
                () -> "compiled beside it: " + together + "\nread off the path: " + offThePath);
    }
}
