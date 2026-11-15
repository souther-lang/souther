package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rewrite of a walk is decided within the runs a rewrite is given, where a row that tells it
 * from the walk exists, wherever in the module the row that shows it is written.
 *
 * <p>The sum reads the amount of a line and the other walk reads the payer. Lists that differ only
 * where neither reads are one list to a walk, and rows the body answered alike on show the same
 * thing, so a search that starts from the rows in the order they were written and grows each with
 * every value in turn spends its runs on the same thing again and again.
 */
class AWalkRewriteIsToldApartWhereItsStepReadsTest {

    private static final List<String> ROWS_OF_THE_AMOUNTS = List.of(
            "| \"a\" : ([ Line { payer = A, amount = 0 } ]) -> [ ]",
            "| \"b\" : ([ Line { payer = B, amount = 0 } ]) -> [ ]",
            "| \"c\" : ([ Line { payer = C, amount = 0 } ]) -> [ ]",
            "| \"d\" : ([ Line { payer = D, amount = 0 } ]) -> [ ]",
            "| \"e\" : ([ Line { payer = E, amount = 0 } ]) -> [ ]",
            "| \"f\" : ([ Line { payer = F, amount = 0 } ]) -> [ true ]",
            "| \"big\" : ([ Line { payer = A, amount = 100000 } ]) -> [ true ]",
            "| \"under\" : ([ Line { payer = A, amount = 99999 } ]) -> [ ]");

    private static final String AMOUNTS_BESIDE_PAYERS_HEAD = """
            module repro.amounts

            data Payer = A | B | C | D | E | F

            data Line = { payer: Payer, amount: Int }

            let total (ls: List<Line>): Int = List.sum(List.map(l -> l.amount, ls))

            let paidByF (p: Payer): Bool =
                match p with
                    | A -> false
                    | B -> false
                    | C -> false
                    | D -> false
                    | E -> false
                    | F -> true

            behavior check : (ls: List<Line>) -> List<Bool>
            let check (ls) = List.filter(b -> b, [ total(ls) >= 100000, List.any(l -> paidByF(l.payer), ls) ])

            example check
            """;

    private static String amountsBesidePayers(List<String> rows) {
        return AMOUNTS_BESIDE_PAYERS_HEAD + String.join("\n    ", rows) + "\n";
    }

    @Test
    void listsThatDifferWhereNoStepReadsAreOneCandidate() {
        assertEquals(List.of(), undecided(measured(amountsBesidePayers(ROWS_OF_THE_AMOUNTS))));
    }

    /**
     * Where the row that matters is written is not what decides the rewrite: the rows the body
     * answered differently on are the ones the search starts from, whichever is written first.
     * The row of the payer that matters is one, and the row of the amount that does is the other.
     */
    @Test
    void theOrderTheRowsAreWrittenInDoesNotDecideTheRewrite() {
        for (int moved : List.of(5, 6)) {
            String theRow = ROWS_OF_THE_AMOUNTS.get(moved);
            List<String> theOthers = new ArrayList<>(ROWS_OF_THE_AMOUNTS);
            theOthers.remove(theRow);
            List<Integer> failing = new ArrayList<>();
            for (int at = 0; at <= theOthers.size(); at++) {
                List<String> rows = new ArrayList<>(theOthers);
                rows.add(at, theRow);
                if (!undecided(measured(amountsBesidePayers(rows))).isEmpty()) {
                    failing.add(at);
                }
            }
            assertEquals(List.of(), failing, "where " + theRow + " is written");
        }
    }

    private static List<String> undecided(Compilation compilation) {
        return page(compilation).lines().map(String::strip)
                .filter(line -> line.startsWith("? not decided whether a row would come out"))
                .toList();
    }

    private static String page(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(compilation);
    }
}
