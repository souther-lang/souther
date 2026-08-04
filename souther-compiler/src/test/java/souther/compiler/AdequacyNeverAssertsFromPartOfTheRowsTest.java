package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One rule, asked of every measure at once.
 *
 * <p>The rule is: <em>found</em> may be said from part of the rows, and <em>not found</em> may not.
 * Every measure here answers over a population, and each of them has at some point claimed the second
 * from an incomplete one — the signature, the positions, the combinations, the boundaries, the arms,
 * and the generator, each found separately, each fixed separately.
 *
 * <p>So this asks all of them together. It walks what a report can say about one behavior and fails on
 * any measure that reports a gap while calling itself complete, over models where something was
 * demonstrably not read. A new measure added later is covered by the same walk, and a new way for a
 * reading to go missing shows up in every measure at once rather than in whichever one someone
 * happened to look at.
 */
class AdequacyNeverAssertsFromPartOfTheRowsTest {

    /**
     * A model, with the budget the compile that reads it is given.
     *
     * <p>The two here want opposite budgets, which is why it is carried beside the source rather than
     * set for the run: one is a row that never comes back, and waiting the default out reaches the
     * same answer later, while the other walks four thousand nodes to spend the observation budget and
     * would be reported as a row that does not terminate if it were held to the first one's.
     */
    private record Unreadable(String source, java.time.Duration budget) {}

    /** Models where something a measure would want to read was not read, each in a different way. */
    private static List<Unreadable> unreadableInSomeWay() {
        return List.of(
                // a row that never finishes: its state is dropped rather than read
                new Unreadable("""
                module example.a

                data Yes
                data No
                data Flag = Yes | No

                data Amount = Int
                    invariant value >= 0

                data Draft = { flag: Flag, cost: Amount }
                data Ok = { n: Int }
                data Big = { n: Int }

                partial let spin (n: Int): Int = spin(n)

                behavior take : (request: Draft) -> Ok | Big
                    constructs Ok, Big

                let take (request) = {
                    guard request.cost.value <= 100 else Big { n = spin(1) }
                    Ok { n = request.cost.value }
                }

                example take
                    | (Draft { flag = Yes, cost = Amount(500) }) -> Big { n = 0 }
                """, DoesNotComeBack.BUDGET),
                // a value past the observation's limits: the position is there and unreadable
                new Unreadable(budgetSpent(), null));
    }

    private static String budgetSpent() {
        StringBuilder inner = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            inner.append(i == 0 ? "" : ", ").append("Item { a = \"").append(i)
                    .append("\", b = \"").append(i).append("\", c = \"").append(i).append("\" }");
        }
        StringBuilder groups = new StringBuilder();
        for (int i = 0; i < 64; i++) {
            groups.append(i == 0 ? "" : ", ")
                    .append("Group { items = [ ").append(inner).append(" ] }");
        }
        return """
                module example.b

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Yes
                data No
                data Flag = Yes | No

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }

                data Draft = { groups: List<Group>, cost: Amount, flag: Flag }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.cost.value }

                example take
                    | (Draft { groups = [ %s ], cost = Amount(0), flag = Yes }) -> Ok { n = 0 }
                """.formatted(groups);
    }

    /** Compiles are shared between the cases that read the same model: each of the three walks the
     * same two, and a compilation answers the same questions however many times it is asked. */
    private static final Map<String, Compilation> COMPILED = new java.util.LinkedHashMap<>();

    private static Compilation measured(Unreadable model) {
        return COMPILED.computeIfAbsent(model.budget() + ":" + model.source(),
                _ -> measured(model.source(), model.budget()));
    }

    private static Compilation measured(String source) {
        return measured(source, null);
    }

    private static Compilation measured(String source, java.time.Duration budget) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        if (budget != null) {
            compilation.withExampleBudget(budget);
        }
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * No measure names a gap while calling itself complete, where something went unread.
     *
     * <p>What each measure calls a gap is its own — an unspecified case, an uncovered class, an unmet
     * boundary, an unreached arm, an untried combination — and what they have in common is that all of
     * them are the sentence "nothing does this", which needs every row to have been read.
     */
    @Test
    void noMeasureNamesAGapWhileCallingItselfComplete() {
        for (Unreadable model : unreadableInSomeWay()) {
            Compilation compilation = measured(model);
            String module = compilation.modules().get(0);
            List<String> wrong = new ArrayList<>();

            Adequacy.SignatureEvidence signature = compilation.db()
                    .ask(new Adequacy.Witnesses(module)).value().get("take");
            if (signature.status() == MeasurementStatus.COMPLETE) {
                if (!signature.output().unspecified().isEmpty()) {
                    wrong.add("signature output: " + signature.output().unspecified());
                }
                signature.inputs().stream().filter(in -> !in.unspecified().isEmpty())
                        .forEach(in -> wrong.add("signature input: " + in.unspecified()));
            }

            PartitionEvidence partition = compilation.db()
                    .ask(new Adequacy.Coverage(module)).value().get("take");
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                if (axis.status() == MeasurementStatus.COMPLETE && !axis.uncovered().isEmpty()) {
                    wrong.add("axis " + axis.path() + ": " + axis.uncovered());
                }
            }
            for (PartitionEvidence.BoundaryCoverage boundary : partition.boundaries()) {
                if (boundary.status() == MeasurementStatus.COMPLETE && !boundary.hit()) {
                    wrong.add("boundary " + boundary.axis() + " = " + boundary.value());
                }
            }
            if (partition.pairs().status() == MeasurementStatus.COMPLETE
                    && partition.pairs().unknown() > 0) {
                wrong.add("pairs: " + partition.pairs().unknown() + " untried");
            }

            Adequacy.BranchEvidence branch = compilation.db()
                    .ask(new Adequacy.BranchCoverage(module)).value().get("take");
            if (branch.status() == MeasurementStatus.COMPLETE && !branch.unreached().isEmpty()) {
                wrong.add("branch: " + branch.unreached().size() + " unreached");
            }

            assertEquals(List.of(), wrong, module + " asserted a gap over rows it did not read");
        }
    }

    /** And the status over them says so, so a reader who only looks at the top is not misled. */
    @Test
    void theReportSaysItCouldNotBeMadeCompletely() {
        for (Unreadable model : unreadableInSomeWay()) {
            AdequacyReport report = AdequacyReport.of(measured(model));
            assertEquals(MeasurementStatus.PARTIAL, report.status(),
                    report.modules().get(0).module());
            assertEquals(MeasurementStatus.PARTIAL,
                    report.modules().get(0).behaviors().get(0).status());
        }
    }

    /**
     * Nor does the generator hand out work from it.
     *
     * <p>The strongest form of the same claim. A warning says nothing does this; a generated row says
     * <em>go and write this</em>, and the row may be one that is already there.
     */
    @Test
    void nothingIsGeneratedFromRowsThatWereNotRead() {
        for (Unreadable model : unreadableInSomeWay()) {
            Compilation compilation = measured(model);
            String module = compilation.modules().get(0);
            Map<String, Adequacy.Filling> generated =
                    compilation.db().ask(new Adequacy.Generated(module)).value();
            assertNotNull(generated);

            assertEquals("", GeneratedRows.of(module, generated, true), module);
        }
    }

    /** Where everything was read, the measures do speak — or this would pass by saying nothing. */
    @Test
    void aModelNothingWentWrongInStillReportsItsGaps() {
        Compilation compilation = measured("""
                module example.fine

                data Yes
                data No
                data Flag = Yes | No

                data Amount = Int
                    invariant value >= 0

                data Draft = { flag: Flag, cost: Amount }
                data Ok = { n: Int }
                data Big = { n: Int }

                behavior take : (request: Draft) -> Ok | Big
                    constructs Ok, Big

                let take (request) = {
                    guard request.cost.value <= 100 else Big { n = 0 }
                    Ok { n = request.cost.value }
                }

                example take
                    | (Draft { flag = Yes, cost = Amount(50) }) -> Ok { n = 50 }
                """);
        String module = compilation.modules().get(0);
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage(module)).value().get("take");

        assertEquals(MeasurementStatus.COMPLETE, AdequacyReport.of(compilation).status());
        assertTrue(partition.axes().stream().anyMatch(a -> !a.uncovered().isEmpty()),
                "a class nothing is in");
        assertTrue(partition.boundaries().stream().anyMatch(b -> !b.hit()),
                "a boundary nothing is at");
        assertTrue(partition.pairs().unknown() > 0, "a combination nothing reaches");
        assertFalse(compilation.db().ask(new Adequacy.BranchCoverage(module)).value()
                .get("take").unreached().isEmpty(), "an arm nothing goes through");
        assertFalse(GeneratedRows.of(module,
                compilation.db().ask(new Adequacy.Generated(module)).value(), true).isEmpty(),
                "and rows offered for them");
    }
}
