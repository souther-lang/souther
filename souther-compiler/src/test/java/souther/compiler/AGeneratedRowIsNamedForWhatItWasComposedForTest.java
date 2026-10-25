package souther.compiler;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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

                if accrued >= policy.cap.value then policy.cap.value else accrued
            }

            example fee
                | "under the cap" : (5, Policy { rate = Rate(10), cap = Cap(500) }) -> 50
            """;

    /** The same, and a row meeting `policy.cap = 0` and no other line. */
    private static final String POLICY_AND_A_ROW_AT_THE_CAP = POLICY + """
                | "a cap of nothing caps everything" : (5, Policy { rate = Rate(10), cap = Cap(0) }) -> 0
            """;

    /** The names the block's rows are written with, in its order. */
    private static List<String> names(String block) {
        return RowsOfABlock.of(block).stream().flatMap(row -> row.name().stream()).toList();
    }

    @Test
    void noTwoRowsOfOneBehaviorAreOfferedUnderOneName() {
        String block = block(LIMIT);
        Map<String, List<String>> byBehavior = new LinkedHashMap<>();
        for (RowsOfABlock.Row row : RowsOfABlock.of(block)) {
            row.name().ifPresent(name -> byBehavior
                    .computeIfAbsent(row.behavior(), _ -> new ArrayList<>()).add(name));
        }
        List<String> offered = byBehavior.getOrDefault("submit", List.of());

        // A claim about names holds of nothing where no row carries one: the two tiers the row for
        // the ceiling does not hold are each a row composed for that tier alone.
        assertTrue(offered.size() >= 2, () -> "rows of one behavior are named: " + block);

        byBehavior.forEach((behavior, named) -> assertEquals(named.size(),
                new LinkedHashSet<>(named).size(),
                "a name says which row of " + behavior + " it is, so no two share one: " + named));
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

        RowsOfABlock.Row was = RowsOfABlock.at(before, SILVER);
        RowsOfABlock.Row is = RowsOfABlock.at(after, SILVER);
        assertEquals(Optional.of("request.tier=Silver"), was.name(), before);
        assertEquals(Optional.of("request.tier=Silver"), is.name(),
                "and the same name once a row meets the line it stood at: " + after);

        assertTrue(was.fills().contains("value = 0"),
                "a named row still says what else it is handed for: " + before);
        assertFalse(is.fills().contains("value = 0"),
                "and stops saying it once another row is handed it: " + after);
    }

    /**
     * A class stays offered, and unnamed, when a row settles something else it also sat on.
     *
     * <p>The class over the ceiling is answered by the same values as the arm the guard sends a run
     * down, so its row was composed for several things, carries no name, and says each over itself.
     * A row written for another tier changes neither.
     */
    @Test
    void aRowKeepsWhatItIsOfferedForWhenAnotherRowSettlesWhatItAlsoSatOn() {
        String before = block(LIMIT);
        String after = block(AND_A_ROW);

        String over = "request.cost=100 < x";
        RowsOfABlock.Row was = RowsOfABlock.forThe(before, over);
        RowsOfABlock.Row is = RowsOfABlock.forThe(after, over);
        assertEquals(Optional.empty(), was.name(),
                "a row composed for several things is named for none of them: " + before);
        assertTrue(was.fills().contains(over), "and says each over itself: " + before);
        assertEquals(Optional.empty(), is.name(),
                "and is still, beside the row written by hand: " + after);
        assertTrue(is.fills().contains(over), "saying the class over itself: " + after);
    }

    /**
     * The other direction: what a row settles is the generation's to change. The class the row by
     * hand sits in is offered a row while nothing is in it and is not once a row is, and neither says
     * anything about the row composed for the cell above.
     */
    @Test
    void whatIsOfferedBesideItIsAllowedToChange() {
        String before = block(LIMIT);
        String after = block(AND_A_ROW);

        assertTrue(RowsOfABlock.of(before).stream().anyMatch(row -> row.isFor("request.tier=Silver")),
                "the class the row was written for was owed: " + before);
        assertTrue(RowsOfABlock.of(after).stream().noneMatch(row -> row.isFor("request.tier=Silver")),
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
        assertEquals(Optional.empty(),
                RowsOfABlock.at(before, "(0, Policy { rate = Rate(0), cap = Cap(0) })").name(),
                "the row two lines compose carries no name: " + before);
        // Once the cap's line is met, the cap is the row's to choose, and it is chosen so that the
        // arm answering what accrued could be told from the arm answering the cap.
        assertEquals(Optional.empty(),
                RowsOfABlock.at(after, "(0, Policy { rate = Rate(0), cap = Cap(").name(),
                "and carries none once a row meets one of the two lines: " + after);
        assertEquals(List.of(), names(before), "there is nothing here a cell composed");
        assertEquals(List.of(), names(after), "nor after");
    }
}
