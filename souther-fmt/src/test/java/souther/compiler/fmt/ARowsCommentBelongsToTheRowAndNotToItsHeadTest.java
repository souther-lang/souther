package souther.compiler.fmt;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who owns a comment written above a row. A row of an {@code example} or a {@code fake}, and an arm
 * of a {@code match}, each open with a {@code |} and then something the row is written around — a
 * description, an input, a pattern. A comment above one of those could be about the row or about the
 * thing the row opens with, and it is about the row: it is written above the whole line, in front of
 * the {@code |}, and the description and the pattern never carry one.
 *
 * <p>Which is why a comment written between the {@code |} and what follows it comes out in the same
 * place as one written above the {@code |}. The two are rows here so that the answer is the row's
 * either way round, and not an artefact of where the comment happened to be.
 */
class ARowsCommentBelongsToTheRowAndNotToItsHeadTest {

    record Placing(String name, String source, String expected) {
        @Override
        public String toString() {
            return name;
        }
    }

    static Stream<Placing> placings() {
        return Stream.of(
                new Placing("above an example row",
                        """
                        module m

                        let helper (n: Int) = n

                        example helper
                            // about this row
                            | "doubles" : (2) -> 2
                        """,
                        """
                        module m

                        let helper (n: Int) = n

                        example helper
                            // about this row
                            | "doubles" : (2) -> 2
                        """),

                new Placing("between an example row's bar and its description",
                        """
                        module m

                        let helper (n: Int) = n

                        example helper
                            |
                            // about this row
                            "doubles" : (2) -> 2
                        """,
                        """
                        module m

                        let helper (n: Int) = n

                        example helper
                            // about this row
                            | "doubles" : (2) -> 2
                        """),

                new Placing("above a match arm",
                        """
                        module m

                        data A

                        data B

                        let f (s: Int): Int = match s with
                            // about this arm
                            | A -> 1
                            | B -> 2
                        """,
                        """
                        module m

                        data A

                        data B

                        let f (s: Int): Int =
                            match s with
                                // about this arm
                                | A -> 1
                                | B -> 2
                        """),

                new Placing("between a match arm's bar and its pattern",
                        """
                        module m

                        data A

                        data B

                        let f (s: Int): Int = match s with
                            |
                            // about this arm
                            A -> 1
                            | B -> 2
                        """,
                        """
                        module m

                        data A

                        data B

                        let f (s: Int): Int =
                            match s with
                                // about this arm
                                | A -> 1
                                | B -> 2
                        """),

                new Placing("above a fake row",
                        """
                        module m

                        let helper (n: Int) = n

                        fake helper
                            // about this row
                            | (2) -> 2
                        """,
                        """
                        module m

                        let helper (n: Int) = n

                        fake helper
                            // about this row
                            | (2) -> 2
                        """));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("placings")
    void aCommentAboveARowIsWrittenAboveTheWholeRow(Placing placing) {
        assertEquals(placing.expected(), Formatter.format(placing.source()));
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("placings")
    void andThatIsWhereItStays(Placing placing) {
        assertEquals(placing.expected(), Formatter.format(placing.expected()));
    }
}
