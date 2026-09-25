package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Primary;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The names one form binds at once are written once each (spec §a-declaration-is-made-once): a
 * signature's parameters, a {@code let}'s parameters — a helper's and a behavior implementation's
 * alike — or a lambda's, with every name their patterns bind,
 * one destructuring {@code let}, one {@code match} arm. Each is refused at the second of the two,
 * before anything reads the names — a written name is answered by one binding, and two bindings
 * taken at once under one spelling leave a reader of the name nothing to choose between them.
 *
 * <p>A binding written inside another binding's scope is not this. It is a scope of its own, and
 * the name it binds is in force over it.
 */
class OneBindingNamesEachOfItsNamesOnceTest {

    @Test
    void aSignatureNamingTwoParametersAlikeIsRefusedAtTheSecond() {
        refusedAtTheSecond("""
                module demo exposing ( f )

                behavior f : (twice: Int, twice: Int) -> Int
                let f (x, y) = x
                """, "twice", "the parameters of `f`");
    }

    /** The clause would read {@code twice} as one of the two; it is refused before it is read. */
    @Test
    void aSignatureWithAnEnsuresIsRefusedAtTheParameterNotAtTheClause() {
        refusedAtTheSecond("""
                module demo exposing ( f )

                behavior f : (twice: Int, twice: Int) -> Int
                    ensures value >= twice
                let f (x, y) = x
                """, "twice", "the parameters of `f`");
    }

    @Test
    void aHelpersTwoParametersOfOneNameAreRefused() {
        refusedAtTheSecond("""
                module demo

                let f (twice: Int, twice: Int) = twice
                """, "twice", "the parameters of `f`");
    }

    /** A pattern's names are the parameter list's, whichever parameter wrote them. */
    @Test
    void aNameAPatternParameterBindsCountsAmongTheOtherParameters() {
        refusedAtTheSecond("""
                module demo

                let f ((twice, y): (Int, Int), twice: Int) = twice + y
                """, "twice", "the parameters of `f`");
    }

    @Test
    void anImplementationsParametersAreOneList() {
        refusedAtTheSecond("""
                module demo exposing ( f )

                behavior f : (a: Int, b: Int) -> Int
                let f (twice, twice) = twice
                """, "twice", "the parameters of `f`");
    }

    @Test
    void aLambdasTwoParametersOfOneNameAreRefused() {
        refusedAtTheSecond("""
                module demo

                let f (xs: List<Int>) = List.map((twice, twice) -> twice, xs)
                """, "twice", "the parameters of a lambda");
    }

    @Test
    void aLambdasPatternIsReadWithItsOtherParameters() {
        refusedAtTheSecond("""
                module demo

                let f (xs: List<Int>) = List.map(((twice, y), twice) -> twice, xs)
                """, "twice", "the parameters of a lambda");
    }

    @Test
    void aTuplePatternOfOneNameTwiceIsRefused() {
        refusedAtTheSecond("""
                module demo

                let f (p: (Int, Int)) = {
                    let (twice, twice) = p
                    twice
                }
                """, "twice", "one pattern");
    }

    /** What a record pattern binds is the name after {@code =}, not the field it reads. */
    @Test
    void aRecordPatternBindingTwoFieldsUnderOneNameIsRefused() {
        refusedAtTheSecond("""
                module demo

                data R = { a: Int, b: Int }

                let f (r: R) = {
                    let { a = twice, b = twice } = r
                    twice
                }
                """, "twice", "one pattern");
    }

    @Test
    void aMatchArmBindingItsFieldAndItsValueAlikeIsRefused() {
        refusedAtTheSecond("""
                module demo

                data A = { twice: Int }
                data B = { n: Int }
                data S = A | B

                let f (s: S) = match s with
                    | A { twice } as twice -> 1
                    | B -> 2
                """, "twice", "one `match` arm", "| A");
    }

    @Test
    void aMatchArmBindingTwoFieldsAlikeIsRefused() {
        refusedAtTheSecond("""
                module demo

                data A = { a: Int, b: Int }
                data B = { n: Int }
                data S = A | B

                let f (s: S) = match s with
                    | A { a = twice, b = twice } -> twice
                    | B -> 2
                """, "twice", "one `match` arm");
    }

    @Test
    void aMatchArmBindingWhatItOpensAndItsValueAlikeIsRefused() {
        refusedAtTheSecond("""
                module demo

                data Id = Int
                data B = { n: Int }
                data S = Id | B

                let f (s: S) = match s with
                    | Id(twice) as twice -> 1
                    | B -> 2
                """, "twice", "one `match` arm");
    }

    /** One name is what the builder settles a spelling to, so two spellings of it are one name. */
    @Test
    void twoSpellingsOfOneCanonicalNameAreOneName() {
        String precomposed = "café";
        String decomposed = "café";
        String src = """
                module demo

                let f (%s: Int, %s: Int) = 1
                """.formatted(precomposed, decomposed);
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1011", e.code(), e.getMessage());
        assertEquals(where(src, src.indexOf(decomposed)), at(src, e),
                "at the second spelling: " + e.getMessage());
    }

    @Test
    void aBindingInsideAnothersScopeTakesItsNameOverThatScope() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                let f (x: Int) = List.map((x) -> x + 1, [x])
                """));
    }

    @Test
    void aDiscardIsNotANameAndMayStandMoreThanOnce() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                let first (p: (Int, Int, Int)) = {
                    let (a, _, _) = p
                    a
                }

                let g (xs: List<(Int, Int)>) = List.map((_) -> 0, xs)
                let h (ps: List<(Int, Int)>) = List.map(((_, _)) -> 0, ps)
                """));
    }

    private static void refusedAtTheSecond(String src, String name, String listedIn) {
        refusedAtTheSecond(src, name, listedIn, "module");
    }

    /** As above, counting the two from where {@code after} is first written. */
    private static void refusedAtTheSecond(String src, String name, String listedIn, String after) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1011", e.code(), e.getMessage());
        int first = src.indexOf(name, src.indexOf(after));
        int second = src.indexOf(name, first + name.length());
        assertEquals(where(src, second), at(src, e), "at the second `" + name + "`: " + e.getMessage());
        assertTrue(e.getMessage().contains(listedIn), "says where the two were written: " + e.getMessage());
    }

    private static String at(String src, CompileException e) {
        return String.valueOf(WhereItSits.in(src,
                ((Primary.InSource) e.diagnostic().primary()).place().region().start()));
    }

    /** The one-based {@code line:column} of the character at {@code offset}. */
    private static String where(String src, int offset) {
        int line = 1;
        int lineStart = 0;
        for (int i = 0; i < offset; i++) {
            if (src.charAt(i) == '\n') {
                line++;
                lineStart = i + 1;
            }
        }
        return line + ":" + (offset - lineStart + 1);
    }
}
