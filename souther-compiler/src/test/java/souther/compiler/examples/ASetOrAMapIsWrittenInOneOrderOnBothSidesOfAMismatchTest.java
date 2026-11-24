package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The parts of a set or a map are written in the order of their values on both sides of a mismatch,
 * where the type is a number or a name over one.
 *
 * <p>A row states a collection and the behavior answers one; a reader is shown the two, and finds
 * what differs by reading them against each other. Written in two orders, a part both hold stands in
 * two places and reads as a difference, so the side the row wrote is put in the order the answer is.
 */
class ASetOrAMapIsWrittenInOneOrderOnBothSidesOfAMismatchTest {

    private static String mismatch(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model)).getMessage();
    }

    private static int count(String text, String part) {
        int found = 0;
        for (int at = text.indexOf(part); at >= 0; at = text.indexOf(part, at + 1)) {
            found++;
        }
        return found;
    }

    @Test
    void aStatedSetAndTheAnswerListTheirCommonElementsAlike() {
        String message = mismatch("""
                module demo

                behavior ids : (n: Int) -> Set<Int>

                let ids (n) = Set.fromList([ 99, 10, 2 ])

                example ids
                    | (0) -> Set.fromList([ 10, 2 ])
                """);

        assertTrue(message.contains("Set.fromList([ 2, 10 ])"), message);
        assertTrue(message.contains("Set.fromList([ 2, 10, 99 ])"), message);
    }

    @Test
    void aSetOfNegativeAndManyDigitNumbersIsInTheOrderOfTheirValues() {
        String message = mismatch("""
                module demo

                behavior ids : (n: Int) -> Set<Int>

                let ids (n) = Set.fromList([ 10, -3, 2, -11, 5 ])

                example ids
                    | (0) -> Set.fromList([ 2, -11 ])
                """);

        // The elements the row also wrote stand where the row's do, then the ones it did not.
        assertTrue(message.contains("Set.fromList([ -11, 2 ])"), message);
        assertTrue(message.contains("Set.fromList([ -11, 2, -3, 5, 10 ])"), message);
    }

    @Test
    void aSetOfANameOverANumberIsInTheOrderOfTheNumbers() {
        String message = mismatch("""
                module demo

                data N = Int

                behavior ns : (n: Int) -> Set<N>

                let ns (n) = Set.fromList([ N(10), N(2), N(9) ])

                example ns
                    | (0) -> Set.fromList([ N(10), N(2) ])
                """);
        String twice = mismatch("""
                module demo

                data N = Int
                data M = N

                behavior ms : (n: Int) -> Set<M>

                let ms (n) = Set.fromList([ M(N(10)), M(N(2)), M(N(9)) ])

                example ms
                    | (0) -> Set.fromList([ M(N(10)), M(N(2)) ])
                """);

        assertTrue(message.contains("Set.fromList([ N(2), N(10), N(9) ])")
                && message.contains("Set.fromList([ N(2), N(10) ])"), message);
        assertTrue(twice.contains("Set.fromList([ M(N(2)), M(N(10)) ])")
                && twice.contains("Set.fromList([ M(N(2)), M(N(10)), M(N(9)) ])"), twice);
    }

    /**
     * A set that is the same on both sides, in a record that differs elsewhere, is still shown. It
     * must read alike on both sides, or the part that agrees looks like the part that does not.
     */
    @Test
    void aSetThatAgreesIsWrittenAlikeBesideAFieldThatDoesNot() {
        String message = mismatch("""
                module demo

                data N = Int
                data Out = { ids: Set<N>, size: Int }

                behavior wrap : (ids: Set<N>) -> Out constructs Out

                let wrap (ids) = Out { ids = ids, size = 3 }

                example wrap
                    | (Set.fromList([ N(10), N(2) ])) -> Out { ids = Set.fromList([ N(10), N(2) ]), size = 2 }
                """);

        // The answer's field and the row's, which agree, read alike.
        assertTrue(message.contains("ids = [ N(2), N(10) ]"), message);
        assertTrue(message.contains("ids = Set.fromList([ N(2), N(10) ])"), message);
        assertEquals(0, count(message, "N(10), N(2)"), message);
    }

    @Test
    void theOrderIsTheSameHoweverTheSetIsBuilt() {
        String forwards = mismatch("""
                module demo

                behavior ids : (n: Int) -> Set<Int>

                let ids (n) = Set.fromList([ 2, 9, 10 ])

                example ids
                    | (0) -> Set.fromList([ 1 ])
                """);
        String backwards = mismatch("""
                module demo

                behavior ids : (n: Int) -> Set<Int>

                let ids (n) = Set.fromList([ 10, 9, 2 ])

                example ids
                    | (0) -> Set.fromList([ 1 ])
                """);

        assertEquals(forwards, backwards);
    }

    @Test
    void aSetOfTextStaysInTheOrderOfItsText() {
        String message = mismatch("""
                module demo

                behavior words : (n: Int) -> Set<String>

                let words (n) = Set.fromList([ "2", "10", "99" ])

                example words
                    | (0) -> Set.fromList([ "2", "10" ])
                """);

        assertTrue(message.contains("Set.fromList([ \"10\", \"2\" ])"), message);
        assertTrue(message.contains("Set.fromList([ \"10\", \"2\", \"99\" ])"), message);
    }
}
