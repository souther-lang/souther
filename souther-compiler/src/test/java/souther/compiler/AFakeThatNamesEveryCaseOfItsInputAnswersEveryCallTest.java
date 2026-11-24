package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code fake} whose rows state every value its parameter can take answers every call, whether
 * or not it ends in a {@code _} row.
 *
 * <p>A row composed for a behavior stands a dependency in with the module's table where the table
 * answers every call, and with a value of its own where it may refuse one. Taken to be the second,
 * a table of every case put {@code []} in where the table answers a list of three, and a walk over
 * that answer never took a second step.
 */
class AFakeThatNamesEveryCaseOfItsInputAnswersEveryCallTest {

    private static String rateOn(String rows, String examples) {
        return """
                module repro.rates

                data Category = Standard | Reduced

                data Change = { from: Int, rate: Int }

                behavior scheduleOf : (k: Category) -> List<Change>

                let rateAsOf (schedule: List<Change>, on: Int): Option<Int> =
                    List.filter(c -> c.from <= on, schedule) |> List.reverse |> List.get(0) |> Option.map(.rate)

                behavior rateOn : (k: Category, on: Int) -> Int
                    depends on scheduleOf

                let rateOn (k, on, scheduleOf) = rateAsOf(scheduleOf(k), on) |> Option.withDefault(0)

                fake scheduleOf
                %s

                example rateOn
                %s
                """.formatted(rows, examples);
    }

    private static final String EVERY_CASE = """
                | (Standard) -> [ Change { from = 10, rate = 3 }, Change { from = 20, rate = 5 }, Change { from = 30, rate = 8 } ]
                | (Reduced) -> [ Change { from = 30, rate = 4 } ]""";

    private static final String EVERY_CASE_BY_A_DEFAULT = """
                | (Standard) -> [ Change { from = 10, rate = 3 }, Change { from = 20, rate = 5 }, Change { from = 30, rate = 8 } ]
                | _ -> [ Change { from = 30, rate = 4 } ]""";

    private static final String ONE_CASE = """
                | (Standard) -> [ Change { from = 10, rate = 3 }, Change { from = 20, rate = 5 }, Change { from = 30, rate = 8 } ]""";

    private static final String EXAMPLES = """
                | "late" : (Standard, 40) -> 8
                | "before" : (Reduced, 29) -> 0""";

    private static final String EXAMPLES_OF_ONE_CASE = """
                | "late" : (Standard, 40) -> 8
                | "before" : (Standard, 5) -> 0""";

    @Test
    void aTableOfEveryCaseIsReadAsATableWithADefaultIs() {
        List<String> byEveryCase = undecided(measured(rateOn(EVERY_CASE, EXAMPLES)));
        List<String> byADefault = undecided(measured(rateOn(EVERY_CASE_BY_A_DEFAULT, EXAMPLES)));

        assertEquals(byADefault, byEveryCase);
        assertEquals(List.of(), byEveryCase);
    }

    @Test
    void aTableMissingACaseIsNotOneThatAnswersEveryCall() {
        Compilation compilation = measured(rateOn(ONE_CASE, EXAMPLES_OF_ONE_CASE));

        assertTrue(!undecided(compilation).isEmpty(), () -> page(compilation));
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
