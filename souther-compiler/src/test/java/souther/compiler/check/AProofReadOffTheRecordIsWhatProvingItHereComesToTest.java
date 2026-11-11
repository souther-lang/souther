package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.semantics.OperationLaw;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Binding the facts of a library that differs from the shipped one reads what proving an operation
 * came to when this compiler was built only where the operation's proofs read nothing that
 * differs, and the facts come out as proving every one of them here makes them.
 *
 * <p>Held over rewrites of the shipped library: one of an operation no other written operation
 * calls, and one of an operation another calls, whose caller is proved again with it. Each is
 * compared with proving the whole library here, observation by observation, statement by
 * statement and operation by operation of what each ends a run for.
 */
class AProofReadOffTheRecordIsWhatProvingItHereComesToTest {

    private static final ValueName.Stdlib.Operation MAP = ValueName.Stdlib.operation("List", "map");
    private static final ValueName.Stdlib.Operation ALL_DISTINCT_BY =
            ValueName.Stdlib.operation("List", "allDistinctBy");
    private static final ValueName.Stdlib.Operation IS_EMPTY =
            ValueName.Stdlib.operation("List", "isEmpty");
    private static final ValueName.Stdlib.Operation FILTER =
            ValueName.Stdlib.operation("List", "filter");

    private record Rewrite(String what, UnaryOperator<String> how) {}

    private static final List<Rewrite> REWRITES = List.of(
            new Rewrite("map lists each image twice",
                    text -> text.replace("acc ++ [f(x)], [], xs)", "acc ++ [f(x), f(x)], [], xs)")),
            new Rewrite("filter keeps each element twice",
                    text -> text.replace("if keep(x) then acc ++ [x] else acc",
                            "if keep(x) then acc ++ [x, x] else acc")),
            new Rewrite("isEmpty asks for one element",
                    text -> text.replace("List.length(xs) == 0", "List.length(xs) == 1")));

    private static Stdlib rewritten(Rewrite rewrite) {
        boolean[] changed = {false};
        Stdlib library = StdlibLoader.load(text -> {
            String out = rewrite.how().apply(text);
            changed[0] |= !out.equals(text);
            return out;
        });
        assertTrue(changed[0], rewrite.what() + " rewrote nothing");
        return library;
    }

    @Test
    void theFactsAreWhatProvingEveryOperationHereMakesThem() {
        for (Rewrite rewrite : REWRITES) {
            Stdlib library = rewritten(rewrite);
            BoundOperationFacts read = OperationFactBinder.bindAll(library);
            BoundOperationFacts proved = OperationFactBinder.bindAll(library, LibraryProofs.PROVING);
            assertEquals(settlings(proved), settlings(read), rewrite.what());
            assertEquals(proved.notProvedOfTheirBodies(), read.notProvedOfTheirBodies(),
                    rewrite.what());
            LibraryEndings readEndings = LibraryEndings.of(library, () -> read);
            LibraryEndings provedEndings = LibraryEndings.of(library, () -> proved);
            for (ValueName.Stdlib.Operation operation : library.helpers().keySet()) {
                assertEquals(provedEndings.of(operation), readEndings.of(operation),
                        rewrite.what() + ": what " + operation + " ends a run for");
            }
        }
    }

    /**
     * And the record is what is read where nothing differs, and not where something does: the
     * operation rewritten and an operation calling it are proved here, and one calling neither is
     * read off the record.
     */
    @Test
    void anOperationIsProvedHereExactlyWhereItsProofsReadWhatDiffers() {
        BoundOperationFacts read = OperationFactBinder.bindAll(rewritten(REWRITES.getFirst()));
        assertFalse(provedWhenBuilt(read, MAP), "the operation rewritten is proved here");
        assertFalse(provedWhenBuilt(read, ALL_DISTINCT_BY),
                "and so is one whose body calls it");
        assertTrue(provedWhenBuilt(read, FILTER), "and one that calls neither is read off");
        assertTrue(provedWhenBuilt(read, IS_EMPTY), "the record");
    }

    private static boolean provedWhenBuilt(BoundOperationFacts facts,
                                           ValueName.Stdlib.Operation operation) {
        Map<OperationLaw.Observed, BoundOperationFacts.Settled> of = facts.settled().get(operation);
        assertFalse(of == null || of.isEmpty(), operation + " has something settled of it");
        return of.values().stream().allMatch(settled ->
                settled instanceof BoundOperationFacts.Settled.ByALaw(var _,
                        BoundOperationFacts.Grounds.ProvedWhenBuilt _));
    }

    /** How each observation is settled, told apart by what settles it and not by how it came to
     *  be known. */
    private static Map<ValueName, Map<OperationLaw.Observed, Object>> settlings(
            BoundOperationFacts facts) {
        Map<ValueName, Map<OperationLaw.Observed, Object>> out = new LinkedHashMap<>();
        facts.settled().forEach((operation, of) -> {
            Map<OperationLaw.Observed, Object> each = new LinkedHashMap<>();
            of.forEach((observed, settled) -> each.put(observed, switch (settled) {
                case BoundOperationFacts.Settled.ByALaw(var law, var _) -> law;
                case BoundOperationFacts.Settled.Unsaid unsaid -> unsaid;
                case BoundOperationFacts.Settled.Open open -> open;
            }));
            out.put(operation, each);
        });
        return out;
    }
}
