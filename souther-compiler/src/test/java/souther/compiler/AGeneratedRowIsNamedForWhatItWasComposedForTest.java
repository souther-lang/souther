package souther.compiler;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code --generate} writes rows, and a written row carries a name — so the generator is a producer
 * of names and is held to what a name is (<<a-row-name-is-unique-within-its-behavior>>).
 *
 * <p>Being distinct within one run is the smaller half. The half that decides the design is that a
 * row's name says which row it is rather than what this run of the generator happened to hand it: a
 * candidate is composed for a cell of the partition or for a line a rule draws, and it is named for
 * that. What it turns out to settle beside that is a fact about the run — a row written elsewhere can
 * meet a line this row also sits on, and the line stops being offered — and naming a row for it made
 * the name move when nothing about the row had.
 *
 * <p>That is what the tests here pin, and they pin the other direction too: the set a row settles is
 * allowed to change. The two are separate facts and only one of them is an identity.
 */
class AGeneratedRowIsNamedForWhatItWasComposedForTest {

    /** The guard divides the amount and nothing divides the tier, so the row for the ceiling holds
     *  the first tier and each other tier has a row composed for it alone, named for it. */
    private static final String LIMIT = """
            module example.limit

            data Amount = Int
                invariant value >= 0

            data Tier = Gold | Silver | Bronze
            data Draft = { cost: Amount, tier: Tier }
            data Submitted = { cost: Amount, tier: Tier }
            data Rejected = { reason: String }

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost, tier = request.tier }
            }
            """;

    /** A row for one of the classes, written by hand — and nothing about the rows below it. */
    private static final String AND_A_ROW = LIMIT + """

            example submit
                | "a silver draft under the ceiling is submitted"
                    : (Draft { cost = Amount(0), tier = Silver })
                    -> Submitted { cost = Amount(0), tier = Silver }
            """;

    /** A row at the bottom of the range in the first tier, which meets the lines the row for the
     *  second tier stood at and settles nothing that row was composed for. */
    private static final String AND_A_ROW_AT_NOTHING = LIMIT + """

            example submit
                | "a gold draft at nothing is submitted"
                    : (Draft { cost = Amount(0), tier = Gold })
                    -> Submitted { cost = Amount(0), tier = Gold }
            """;

    /** The values of the generated row for the second tier, as the block writes them. */
    private static final String SILVER = "(Draft { cost = Amount(0), tier = Silver })";

    /** {@code | "name" : (inputs)} as the block writes it, over lines the formatter may have wrapped. */
    private static final Pattern OFFERED = Pattern.compile("\\|\\s*\"((?:[^\"\\\\]|\\\\.)*)\"\\s*\\n?\\s*:");

    private static String block(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filling = Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(filling, "the model under test compiles");
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(compilation.modules().get(0))),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();
    }

    /** Two minimum edges of one behavior, which compose one row between them. */
    private static final String POLICY = """
            module example.policy

            data Rate = Int
                invariant nonNegative = value >= 0

            data Cap = Int
                invariant nonNegative = value >= 0

            data Policy =
                { rate: Rate
                , cap: Cap
                }

            behavior fee : (days: Int, policy: Policy) -> Int

            let fee (days, policy) = {
                let accrued = days * policy.rate.value

                if accrued > policy.cap.value then policy.cap.value else accrued
            }

            example fee
                | "under the cap" : (5, Policy { rate = Rate(10), cap = Cap(500) }) -> 50
            """;

    /** The same, and a row meeting `policy.cap = 0` and no other line. */
    private static final String POLICY_AND_A_ROW_AT_THE_CAP = POLICY + """
                | "a cap of nothing caps everything" : (5, Policy { rate = Rate(10), cap = Cap(0) }) -> 0
            """;

    /** The names the block offers, in the order it writes them — one for every row written with
     *  a name, or a failure, since a row whose name this does not read is a row nothing checks. */
    private static List<String> names(String block) {
        List<String> found = new ArrayList<>();
        String rows = block.replace("//", "");
        Matcher m = OFFERED.matcher(rows);
        while (m.find()) {
            found.add(m.group(1));
        }
        assertEquals(namedRowsIn(rows), found.size(),
                () -> "a name is read for every row the block writes with one: " + block);
        return found;
    }

    /** How many rows {@code rows} writes with a name, each of the others written with none. */
    private static long namedRowsIn(String rows) {
        List<String> written = rows.lines().map(String::trim)
                .filter(line -> line.startsWith("|")).toList();
        written.forEach(line -> assertTrue(line.startsWith("| \"") || line.startsWith("| ("),
                () -> "a row is written with a name or with none: " + line));
        return written.stream().filter(line -> line.startsWith("| \"")).count();
    }

    @Test
    void noTwoRowsOfOneBehaviorAreOfferedUnderOneName() {
        String block = block(LIMIT);
        List<String> offered = names(block);

        // A claim about names holds of nothing where no row carries one: the two tiers the row for
        // the ceiling does not hold are each a row composed for that tier alone.
        assertTrue(offered.size() >= 2, () -> "rows of one behavior are named: " + block);

        Set<String> distinct = new LinkedHashSet<>(offered);
        assertEquals(offered.size(), distinct.size(),
                "a name says which row it is, so no two rows share one: " + offered);
    }

    /**
     * A row keeps its name when another row meets a line it stood at.
     *
     * <p>The row for the second tier is composed for that tier and stands at the bottom of the
     * amount's range, so it is the row handed for the points there as well. A row written at the
     * bottom of the range in another tier meets those points and settles nothing the row for the
     * second tier was composed for, so its values and its name stay. What it is handed for beside
     * that is said over it while it is handed it, and not after.
     */
    @Test
    void aRowKeepsItsNameWhenAnotherRowMeetsALineItStoodAt() {
        String before = block(LIMIT);
        String after = block(AND_A_ROW_AT_NOTHING);

        assertEquals(Optional.of("request.tier=Silver"), nameOfTheRowAt(before, SILVER), before);
        assertEquals(Optional.of("request.tier=Silver"), nameOfTheRowAt(after, SILVER),
                "and the same name once a row meets the line it stood at: " + after);

        assertTrue(saidOverTheRowAt(before, SILVER).contains("value = 0"),
                "a named row still says what else it is handed for: " + before);
        assertTrue(!saidOverTheRowAt(after, SILVER).contains("value = 0"),
                "and stops saying it once another row is handed it: " + after);
    }

    /** The name of the one row the block writes at {@code inputs}, or none where it has none. */
    private static Optional<String> nameOfTheRowAt(String block, String inputs) {
        String row = theRowAt(block, inputs);
        Matcher m = OFFERED.matcher(row);
        return m.find() ? Optional.of(m.group(1)) : Optional.empty();
    }

    /** What the block says over the one row it writes at {@code inputs}, a line apiece. */
    private static List<String> saidOverTheRowAt(String block, String inputs) {
        List<String> lines = block.lines().toList();
        int at = lines.indexOf(theRowAt(block, inputs));
        List<String> said = new ArrayList<>();
        for (int i = at - 1; i >= 0 && lines.get(i).startsWith("// fills "); i--) {
            said.addFirst(lines.get(i).substring("// fills ".length()));
        }
        return said;
    }

    /** The one row the block writes at {@code inputs}. */
    private static String theRowAt(String block, String inputs) {
        List<String> at = block.lines()
                .filter(line -> line.startsWith("    | ") && line.contains(inputs)).toList();
        assertEquals(1, at.size(), () -> "one row is written at " + inputs + ": " + block);
        return at.getFirst();
    }

    /**
     * A class stays offered when a row settles something else it also sat on.
     *
     * <p>The class over the ceiling is answered by the same values as the arm the guard sends a run
     * down, so its row was composed for several things, carries no name, and says each over itself.
     * What would be a defect is the class going unmentioned once a row is written for another tier.
     */
    @Test
    void aRowKeepsWhatItIsOfferedForWhenAnotherRowSettlesWhatItAlsoSatOn() {
        String before = block(LIMIT);
        String after = block(AND_A_ROW);

        String over = "request.cost=100 < x";
        assertTrue(offeredFor(before).contains(over),
                "the class is owed before anything is written: " + before);
        assertTrue(offeredFor(after).contains(over),
                "and is still what a row is offered for, beside the row written by hand: " + after);
    }

    /** What the block says its rows are for, whether as a name or as a line over an unnamed row. */
    private static List<String> offeredFor(String block) {
        List<String> found = new ArrayList<>(names(block));
        block.lines().filter(line -> line.contains("fills "))
                .map(line -> line.substring(line.indexOf("fills ") + "fills ".length()))
                .forEach(found::add);
        return found;
    }

    /**
     * The other direction: what a row settles is the generation's to change. The line at the bottom of
     * the range is offered while nothing meets it and is not offered once a row does, and neither says
     * anything about the row named for the cell above.
     */
    @Test
    void whatIsOfferedBesideItIsAllowedToChange() {
        List<String> before = offeredFor(block(LIMIT));
        List<String> after = offeredFor(block(AND_A_ROW));

        assertTrue(before.contains("request.tier=Silver"),
                "the class the row was written for was owed: " + before);
        assertTrue(!after.contains("request.tier=Silver"),
                "and is not owed once a row sits in it: " + after);
    }

    /**
     * Two lines composing one row is the case with no cell to name it and no line that can. Each
     * probe fills what its own edge does not name from the bottom of the other's domain, so the two
     * minimum edges here compose one row; which of them is still owed is what an unrelated row
     * changes, and a row named for whichever was offered would be renamed by that. It is offered
     * without a name, and stays that way.
     */
    @Test
    void aRowTwoLinesComposeIsOfferedWithoutAName() {
        String before = block(POLICY);
        String after = block(POLICY_AND_A_ROW_AT_THE_CAP);
        String written = "| (0, Policy { rate = Rate(0), cap = Cap(0) }) -> <?>";
        // Once the cap's line is met, the cap is the row's to choose, and it is chosen so that the
        // arm answering what accrued could be told from the arm answering the cap.
        Pattern unnamed = Pattern.compile(
                " {4}\\| \\(0, Policy \\{ rate = Rate\\(0\\), cap = Cap\\([0-9]+\\) \\}\\) -> <\\?>");

        assertTrue(before.contains(written), "the row two lines compose carries no name: " + before);
        assertTrue(after.lines().anyMatch(line -> unnamed.matcher(line).matches()),
                "and carries none once a row meets one of the two lines: " + after);
        assertEquals(List.of(), names(before), "there is nothing here a cell composed");
        assertEquals(List.of(), names(after), "nor after");
    }
}
