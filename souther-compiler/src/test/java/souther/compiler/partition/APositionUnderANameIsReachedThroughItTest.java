package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record under a name is a record, and everything that reaches into one goes through the name.
 *
 * <p>{@link souther.compiler.check.TypeView} says a {@code data SlotN = Slot} is the product
 * {@code Slot}, so the derivation takes the position apart and the axes are at its fields. That is
 * one of four readings of the same position, and the other three are what a measure is made of:
 * a row writes {@code SlotN(Slot { flag = true })} and something has to read it back, something has
 * to write one, and the clauses relating the record's fields have to reach them.
 *
 * <p>Held together because three of them were missing while the first was there. The axis was
 * derived and no row could be classified at it, no row could be generated for it, and the record's
 * own rules about its fields were dropped on the way in — a position measured by a measure that
 * could not measure it.
 *
 * <p>Against the bare form in every row, because that is what the claim is: a name is how a value
 * is written and not what it is, so the two forms are measured alike.
 */
class APositionUnderANameIsReachedThroughItTest {

    private static final String FLAGS = """
            module demo

            data Ok
            data Slot = { flag: Bool }
            data SlotN = Slot

            behavior bare : (x: Slot) -> Ok
            let bare (x) = Ok

            behavior wrapped : (x: SlotN) -> Ok
            let wrapped (x) = Ok

            example bare
                | (Slot { flag = true }) -> Ok

            example wrapped
                | (SlotN(Slot { flag = true })) -> Ok
            """;

    /** A record whose clauses relate its fields, which is what a position wearing a name would drop
     *  on the way to them. */
    private static final String PAIRS = """
            module demo

            data Ok
            data N = Int invariant value >= 0 && value <= 10
            data Pair = { low: N, high: N } invariant low.value < high.value
            data PairN = Pair

            behavior bare : (p: Pair) -> Ok
            let bare (p) = Ok

            behavior wrapped : (p: PairN) -> Ok
            let wrapped (p) = Ok
            """;

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static PartitionEvidence evidence(Compilation compilation, String behavior) {
        PartitionEvidence found = compilation.db()
                .ask(new Adequacy.Coverage("demo")).value().get(behavior);
        assertNotNull(found, behavior + " was measured");
        return found;
    }

    /** Derive: the position is taken apart at the fields of what the name is written over. */
    @Test
    void theFieldsUnderTheNameAreWhereThePositionDivides() {
        Compilation compilation = measured(FLAGS);

        assertEquals(List.of("x.flag"), evidence(compilation, "wrapped").axes().stream()
                .map(PartitionEvidence.AxisCoverage::path).toList());
        assertEquals(List.of("true", "false"),
                evidence(compilation, "wrapped").axes().get(0).classes());
    }

    /** Read: a row that wrote the value under the name is counted at the class it is in. */
    @Test
    void aRowWrittenUnderTheNameIsReadBackThroughIt() {
        Compilation compilation = measured(FLAGS);

        assertEquals(Set.of("true"), evidence(compilation, "wrapped").axes().get(0).rows().covered());
        assertEquals(evidence(compilation, "bare").axes().get(0).rows().covered(),
                evidence(compilation, "wrapped").axes().get(0).rows().covered(),
                "a name is how a value is written, not what it is");
    }

    /** Write: what the row for the class nothing covers is, which is the value under the name. */
    @Test
    void aRowOfferedForThePositionIsWrittenUnderTheName() {
        String rows = GeneratedRows.of(measured(FLAGS), "demo", "wrapped", true,
                SourceNameResolver.identity()).text();

        assertTrue(rows.contains("(SlotN(Slot { flag = false }))"), rows);
    }

    /**
     * And the rules the record writes about its fields reach them.
     *
     * <p>Read off the name instead, a wrapped record has no clauses at all: the boundaries its
     * fields owe come from the ends its own rules leave them, and the rows built for those have to
     * hold the clause relating the two. Both are counted here, and the second is what a generated
     * row shows — a `low` at the top of its range beside a `high` that is still above it.
     */
    @Test
    void theRulesARecordWritesAboutItsFieldsReachThemUnderAName() {
        Compilation compilation = measured(PAIRS);

        assertEquals(evidence(compilation, "bare").boundaries().size(),
                evidence(compilation, "wrapped").boundaries().size(),
                "the same record is bounded the same way under a name");
        assertTrue(evidence(compilation, "wrapped").boundaries().size() >= 4);

        String rows = GeneratedRows.of(compilation, "demo", "wrapped", true,
                SourceNameResolver.identity()).text();
        assertTrue(rows.contains("(PairN(Pair { low = N(9), high = N(10) }))"), rows);
    }
}
