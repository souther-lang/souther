package souther.compiler.fmt;

import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How far one level of nesting moves a line. Four columns is what the formatter writes, but a fixture
 * that observes a four somewhere says only that: it holds equally for a formatter that indents the
 * first level by four and the second by six. What is asserted here is the difference between one
 * level and the next, over constructs deep enough for there to be three of them.
 */
class EachLevelOfNestingIndentsByFourTest {

    private static final int INDENT = 4;

    /**
     * @param levels how many levels below the left margin the construct reaches. Written down so that
     *     a fixture that stopped nesting — because a name got shorter and a group fitted after all —
     *     fails rather than asking about fewer levels than it was written for.
     */
    record Nesting(String name, String source, int levels) {
        @Override
        public String toString() {
            return name + ", " + levels + " levels deep";
        }
    }

    static Stream<Nesting> nestings() {
        return Stream.of(
                new Nesting("calls inside calls",
                        """
                        module m exposing ( f )

                        let f (a: Int): Int =
                            oneCall(twoCall(threeCall(fourCall(aVeryLongArgumentNameThatKeepsGoing, anotherVeryLongArgumentNameHere))))
                        """,
                        4),

                new Nesting("a list inside a record inside a call",
                        """
                        module m exposing ( f )

                        let f (a: Int): Int =
                            oneCall(Receipt { theFirstField = [anElementName, anotherElementName, aThirdElementName, aFourthOne] })
                        """,
                        3),

                new Nesting("a match inside a block",
                        """
                        module m exposing ( f )

                        let f (a: Int): Int = {
                            let x = match a with
                                | Zero -> aVeryLongFunctionCall(withSomeArgument, andAnotherArgument, andAThird)
                                | One -> beta
                            x
                        }
                        """,
                        2),

                new Nesting("the departures of a guard inside a block",
                        """
                        module m exposing ( f )

                        let f (a: Int): Int = {
                            guard Amount(a) as amount else
                                | one -> Refused
                                | two -> Denied
                            amount
                        }
                        """,
                        2),

                new Nesting("a clause under a signature, broken over its names",
                        """
                        module m exposing ( b )

                        behavior b : (a: A) -> R
                            constructs FirstConstructed, SecondConstructed, ThirdConstructed, FourthConstructed, FifthConstructed, SixthConstructed
                        """,
                        2),

                new Nesting("an example row, its parts and a call inside one",
                        """
                        module m exposing ( j )

                        example j
                            | "a description long enough that the row is written over more than one line"
                                : (aFunctionCall(theFirstArgumentName, theSecondArgumentName, theThirdArgumentName))
                                -> Accepted
                        """,
                        2));
    }

    /**
     * The indents the formatted source uses, in increasing order — counted in spaces, and asserting
     * that spaces are what they are made of. Measuring the width of whatever leading whitespace a
     * line has would let a formatter indent each level with four tabs and answer four; if canonical
     * surface syntax is ever normative, a tab and four spaces are different text however they read.
     */
    private static List<Integer> indentsOf(String formatted) {
        TreeSet<Integer> seen = new TreeSet<>();
        for (String line : formatted.split("\n", -1)) {
            if (line.isBlank()) {
                continue;
            }
            int indent = line.length() - line.stripLeading().length();
            assertEquals(" ".repeat(indent), line.substring(0, indent),
                    "a line is indented with something other than spaces: " + line);
            seen.add(indent);
        }
        return new ArrayList<>(seen);
    }

    /**
     * Every level the construct reaches is one indent further in than the level above it, and by the
     * same amount each time. Stated over the whole ladder rather than as "an indent is a multiple of
     * four": a formatter that skipped a level would satisfy the multiple and not this.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("nestings")
    void oneLevelDeeperIsOneIndentFurtherIn(Nesting nesting) {
        String formatted = Formatter.format(nesting.source());
        List<Integer> indents = indentsOf(formatted);
        assertEquals(0, indents.get(0).intValue(),
                nesting.name() + ": the outermost line is not at the margin, in:\n" + formatted);
        for (int i = 1; i < indents.size(); i++) {
            assertEquals(INDENT, indents.get(i) - indents.get(i - 1),
                    nesting.name() + ": the indents used are " + indents + ", in:\n" + formatted);
        }
    }

    /** And the construct really is as deep as the row says, so the ladder above has rungs on it. */
    @ParameterizedTest(name = "{0}")
    @MethodSource("nestings")
    void theFixtureNestsAsDeeplyAsItClaims(Nesting nesting) {
        String formatted = Formatter.format(nesting.source());
        List<Integer> indents = indentsOf(formatted);
        assertEquals(nesting.levels(), indents.size() - 1,
                nesting.name() + ": the indents used are " + indents + ", in:\n" + formatted);
    }

    /** At least one of them is deep enough for this to be about a difference and not about a four. */
    @org.junit.jupiter.api.Test
    void andOneOfThemGoesThreeLevelsDown() {
        assertTrue(nestings().anyMatch(n -> n.levels() >= 3),
                "no fixture reaches three levels, so a formatter that indented the first level by"
                        + " four and the next by six would pass every row");
    }
}
