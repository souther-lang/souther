package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.BodyReading;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A build that measures some behaviors only reads the bodies of those, and says of them what a
 * build that measures every behavior says.
 *
 * <p>A line a declaration drew is owed once however many behaviors carry the type, so a behavior
 * that is measured shares it with ones that are not: a row of any of them at a point of it answers
 * the point. That part of a behavior nobody asked about is read — the lines its declarations draw
 * and where its rows stand on them — and its body is not, which is where the cost of reading it
 * is ({@link Adequacy#bodyReading}).
 *
 * <p>The model has one declaration two behaviors carry, with a row at each of its ends written
 * for a different one of them. So the report of either says the end the other's row stands at is
 * answered, and would say it is owed a row if the other's rows had gone unread.
 */
class ABehaviorABuildDoesNotMeasureIsReadByWhatItDeclaresTest {

    private static final String MODEL = """
            module Main

            data Amount = Int
                invariant value >= 0 && value <= 100

            data Small = { amount: Amount }
            data Large = { amount: Amount }

            behavior near : (amount: Amount) -> Small | Large
                constructs Small, Large
            let near (amount) =
                if amount.value < 50 then Small { amount = amount } else Large { amount = amount }

            behavior far : (amount: Amount) -> Small | Large
                constructs Small, Large
            let far (amount) =
                if amount.value < 20 then Small { amount = amount } else Large { amount = amount }

            example near
                | "the floor" : (Amount(0))  -> Small { amount = Amount(0) }
                | "under"     : (Amount(49)) -> Small { amount = Amount(49) }
                | "at"        : (Amount(50)) -> Large { amount = Amount(50) }
                | "over"      : (Amount(60)) -> Large { amount = Amount(60) }

            example far
                | "the ceiling" : (Amount(100)) -> Large { amount = Amount(100) }
                | "under"       : (Amount(19))  -> Small { amount = Amount(19) }
                | "at"          : (Amount(20))  -> Large { amount = Amount(20) }
            """;

    private static Compilation measuring(Adequacy.Choice choice) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.choose(choice);
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation;
    }

    private static String reportOf(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).only(null, behavior)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theReportOfABehaviorIsTheSameWhetherOrNotTheOthersWereMeasured() {
        Compilation everything = measuring(Adequacy.Choice.EVERYTHING);
        for (String behavior : new String[] {"near", "far"}) {
            Compilation narrowed = measuring(new Adequacy.Choice(null, behavior));

            assertEquals(reportOf(everything, behavior), reportOf(narrowed, behavior),
                    "narrowed to `" + behavior + "`");
        }
    }

    @Test
    void aPointOfASharedLineIsAnsweredByARowOfABehaviorTheBuildDoesNotMeasure() {
        String near = reportOf(measuring(new Adequacy.Choice(null, "near")), "near");

        assertTrue(near.contains("declarations   borders 2   obligations 4/4"),
                () -> "the ceiling of `Amount` is answered by a row of `far`: " + near);
        assertTrue(near.contains("adequacy: satisfied"), () -> near);
    }

    @Test
    void theBodyOfABehaviorTheBuildDoesNotMeasureIsNotRead() {
        Compilation narrowed = measuring(new Adequacy.Choice(null, "near"));
        Db db = narrowed.db();
        Bodies.Elaborated checked = db.ask(new Bodies.Observable("Main")).value();

        assertInstanceOf(BodyReading.Read.class,
                Adequacy.bodyReading(db, "Main", checked, "near"));
        assertInstanceOf(BodyReading.NotInElaboration.class,
                Adequacy.bodyReading(db, "Main", checked, "far"));
    }
}
