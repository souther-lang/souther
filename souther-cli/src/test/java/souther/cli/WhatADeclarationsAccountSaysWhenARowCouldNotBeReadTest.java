package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the block under a module's declarations says about an obligation whose reading was made in
 * part.
 *
 * <p>A row too large to observe leaves every reading of the line short of an answer: nothing was
 * seen at the point and something the reading needs was not read, so what the debt came to is a
 * measurement made in part and no row is known to be at it. That is neither a row anybody has
 * written nor a gap the model has — the value that would answer it may be in the part nobody read —
 * and the account counts it all the same, because a point whose writability is known is a point a
 * row is owed at.
 *
 * <p>The behavior's own block and the module's declarations count the same relation at two grains,
 * so the two numbers on the page are not one another's parts: the lines the body reads are its
 * borders and the rows the type's clause asks for are the module's.
 */
class WhatADeclarationsAccountSaysWhenARowCouldNotBeReadTest {

    /**
     * A model whose one row is past what an observation of it can hold.
     *
     * <p>The size is in the list of groups and the line is on {@code Amount}, so what goes unread is
     * not the coordinate the line is drawn on: the rules of the clause are readable, a row could
     * stand at either end of it, and what nobody can say is whether this row does.
     */
    private static final String TOO_LARGE_TO_OBSERVE = """
            module example.b

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Item = { a: String, b: String, c: String }
            data Group = { items: List<Item> }

            data Draft = { groups: List<Group>, cost: Amount }
            data Ok = { n: Int }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            let someItems (n: Int): List<Item> =
                List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

            let someGroups (n: Int): List<Group> =
                List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

            example take
                | (Draft { groups = someGroups(64), cost = Amount(0) }) -> Ok { n = 0 }
            """;

    /**
     * The count holds four obligations and the block names none of them.
     *
     * <p>Four is what {@code Amount}'s two ends owe: a point against each line and a point away from
     * it, all four of them measured and all four known to be writable. None is met, none is a gap
     * the report writes a line for, and a reader is handed a number with nothing under it to act on.
     */
    @Test
    void theCountHoldsFourObligationsAndTheBlockNamesNoneOfThem() throws Exception {
        Run run = examples(TOO_LARGE_TO_OBSERVE, "--strict");

        assertTrue(run.out().contains("declarations   obligations 0/4"),
                () -> "the module's declarations owe four rows and no row is at one:\n" + run.out());
        assertFalse(run.out().contains("no row is at"),
                () -> "and nothing under the block says which of the four:\n" + run.out());
    }

    /** Nothing the model is short of is refused, the four being points nobody established a gap at. */
    @Test
    void nothingIsRefusedOverThem() throws Exception {
        Run run = examples(TOO_LARGE_TO_OBSERVE, "--strict");

        assertTrue(run.out().contains("adequacy: undetermined"), run.out());
        assertEquals(0, run.code(), run.err());
    }

    /**
     * The behavior's own block owes nothing, the lines under it being the declarations'.
     *
     * <p>Two borders and no obligation: the body reads {@code Amount}'s clause at one position and
     * the rows the clause asks for are owed once for the module, so the two numbers here count
     * different things and neither is a part of the other.
     */
    @Test
    void theBehaviorsBlockCountsBordersAndOwesNothing() throws Exception {
        Run run = examples(TOO_LARGE_TO_OBSERVE);

        assertTrue(run.out().contains("border      borders 2   obligations 0/0"), run.out());
    }

    private record Run(int code, String out, String err) {}

    private static Run examples(String model, String... extra) throws Exception {
        Path file = Files.createTempDirectory("souther-declared-account").resolve("model.sou");
        Files.writeString(file, model);
        List<String> args = new ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(extra));
        PrintStream wasOut = System.out;
        PrintStream wasErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.dispatch(args.toArray(String[]::new));
        } finally {
            System.setOut(wasOut);
            System.setErr(wasErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
