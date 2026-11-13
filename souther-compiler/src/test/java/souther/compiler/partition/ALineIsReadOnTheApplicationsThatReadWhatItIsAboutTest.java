package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.AnApplicationOfAClosure;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line is read on the applications that read what it is about, and on no other.
 *
 * <p>The comparison is read on three applications of a fold over values written out: the first
 * compares an item's {@code n} with three, the second its {@code n} with the greatest a walk over
 * the items has kept, the third its {@code m} with that. The second and third are relations to
 * another value, read as one relation of the comparison; the line parting the values of {@code n}
 * that settle the second is about {@code n}, and is read on the second application alone — the
 * third read nothing about {@code n}.
 */
class ALineIsReadOnTheApplicationsThatReadWhatItIsAboutTest {

    private static final String MODEL = """
            module demo exposing (g, Item, Order)

            data Item = { n: Int, m: Int }
                invariant n >= 0 && n <= 100 && m >= 0 && m <= 100
            data Order = { items: List<Item>, open: Bool }

            behavior g : (o: Order) -> Bool
            let g (o) = List.fold((acc, r) -> acc + List.fold((w, i) ->
                if (if r > 6 then i.m else i.n) > (if r > 4 then w else 3) then i.n else w,
                0, o.items), 0, [3, 5, 7]) <= 50
            """;

    /** Which applications of the fold over the values written out each line on {@code axis} was
     *  read on, by ordinal. */
    private static List<Set<Integer>> readOnAlong(Partitions.Partitioning partitioning,
                                                  String axis) {
        List<Border> lines = new ArrayList<>(partitioning.between());
        partitioning.along().values().forEach(lines::addAll);
        List<Set<Integer>> out = new ArrayList<>();
        for (Border line : lines) {
            if (!line.axis().equals(axis)) {
                continue;
            }
            Set<Integer> ordinals = new TreeSet<>();
            for (AnApplicationOfAClosure one : partitioning.readOn().of(line.origin()).each()) {
                ordinals.add(one.by().getFirst().ordinal());
            }
            out.add(ordinals);
        }
        return out;
    }

    @Test
    void aLinePartingWhatSettlesARelationIsReadOnWhatReadThatRelation() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        Partitions.Partitioning partitioning =
                compilation.db().ask(new Adequacy.Divided("demo", "g")).value();
        List<Set<Integer>> onN = readOnAlong(partitioning, "g/o.items[*].n");
        List<Border> every = new ArrayList<>(partitioning.between());
        partitioning.along().values().forEach(every::addAll);
        assertFalse(onN.isEmpty(), "lines are drawn on n: "
                + every.stream().map(Border::axis).toList());
        assertTrue(onN.contains(Set.of(1)),
                "the line parting what settles the second application's relation: " + onN);
        for (Set<Integer> each : onN) {
            assertFalse(each.contains(2), "the third application read nothing about n: " + onN);
        }
        // A line on m is drawn by the comparison of the total, which stands in no closure.
        for (Set<Integer> each : readOnAlong(partitioning, "g/o.items[*].m")) {
            assertTrue(Set.of(2).containsAll(each), "only the third application read m: " + each);
        }
    }
}
