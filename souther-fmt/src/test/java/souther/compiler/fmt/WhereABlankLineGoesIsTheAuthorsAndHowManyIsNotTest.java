package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Between two members written one to a line, a blank line survives and its size does not.
 *
 * <p>The two halves are one rule. That a paragraph break is there is something the author wrote and
 * the canonical form has no other way to know: a block of nine statements and a block of three
 * groups of three are the same tree, so grouping is the only structure a body has that is not in it.
 * How big the break is carries nothing, so any number of blank lines comes back as one and the
 * canonical form still has one answer per input.
 *
 * <p>Between members a construct writes with a connector — a {@code data}'s fields, a union's cases,
 * an argument list — there is no paragraph break to keep. Those members are a run and what is
 * between two of them is the run's, so a blank line written there is layout and goes.
 *
 * <p>{@link WhatSeparatesTwoItemsComesFromBothOfThemTest} holds the same rule over every pair of
 * top-level items, including the two pairs the file separates whatever the author wrote. This is the
 * block body's half, and the part no pair of top-level items reaches: a blank line inside a nesting.
 */
class WhereABlankLineGoesIsTheAuthorsAndHowManyIsNotTest {

    @Test
    void aBlockKeepsThePlacesItsAuthorLeftABlankLine() {
        assertEquals("""
                module m

                let f (n: Int) = {
                    let x = 1
                    let y = 2

                    let z = 3

                    x + y + z
                }
                """, Formatter.format("""
                module m
                let f (n: Int) = {
                    let x = 1
                    let y = 2

                    let z = 3

                    x + y + z
                }
                """));
    }

    @Test
    void andAnyNumberOfThemIsOne() {
        assertEquals("""
                module m

                let f (n: Int) = {
                    let x = 1

                    x + 1
                }
                """, Formatter.format("""
                module m
                let f (n: Int) = {
                    let x = 1




                    x + 1
                }
                """));
    }

    @Test
    void andWhereTheAuthorLeftNoneThereIsNone() {
        assertEquals("""
                module m

                let f (n: Int) = {
                    let x = 1
                    let y = 2
                    x + y
                }
                """, Formatter.format("""
                module m
                let f (n: Int) = {
                    let x = 1
                    let y = 2
                    x + y
                }
                """));
    }

    /** A comment is a step's, and the paragraph break goes above what it opens rather than between
     *  the comment and the step it is written over. */
    @Test
    void andAParagraphOpensWithItsComment() {
        assertEquals("""
                module m

                let f (n: Int) = {
                    let x = 1

                    // what the rest of it does
                    let y = 2
                    x + y
                }
                """, Formatter.format("""
                module m
                let f (n: Int) = {
                    let x = 1

                    // what the rest of it does
                    let y = 2
                    x + y
                }
                """));
    }

    /** Between the members of a run there is no paragraph to keep. */
    @Test
    void aBlankLineInsideAConstructIsLayoutAndGoes() {
        assertEquals("""
                module m

                data D =
                    { a: Int
                    , b: Int
                    }
                """, Formatter.format("""
                module m
                data D =
                    { a: Int

                    , b: Int
                    }
                """));
    }

    /**
     * A blank line has nothing on it, so it is written with nothing on it. The break that leaves one
     * is inside whatever nesting the member is in, and written with that nesting's indent it would
     * leave spaces on a line a reader sees as empty and an editor strips — which would then be a file
     * {@code fmt --check} and the editor disagree about.
     */
    @Test
    void aBlankLineHasNothingOnIt() {
        String formatted = Formatter.format("""
                module m
                let f (n: Int) = {
                    let x = 1

                    let y = {
                        let z = 2

                        z + 1
                    }
                    x + y
                }
                """);
        List<String> padded = new ArrayList<>();
        for (String line : formatted.split("\n", -1)) {
            if (!line.isEmpty() && line.isBlank()) {
                padded.add("`" + line + "`");
            }
        }
        assertEquals(List.of(), padded, "blank lines with something on them, in:\n" + formatted);
        assertTrue(formatted.contains("\n\n        z + 1"),
                "the blank line inside the nested block is not there, in:\n" + formatted);
    }

    /** And the form each of these comes back in is read back as itself. */
    @Test
    void everyAnswerIsAFixedPoint() {
        for (String source : new String[] {
                """
                module m
                let f (n: Int) = {
                    let x = 1

                    x + 1
                }
                """,
                """
                module m
                let f (n: Int) = {
                    let x = 1
                    x + 1
                }
                """,
                """
                module m
                data A = Int
                data B = Int

                data C = Int
                """}) {
            String once = Formatter.format(source);
            assertEquals(once, Formatter.format(once), once);
        }
    }
}
