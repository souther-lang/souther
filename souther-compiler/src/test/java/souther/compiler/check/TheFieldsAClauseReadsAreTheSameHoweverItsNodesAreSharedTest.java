package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * The fields {@link RecordRules#readFrom} finds in a clause are those it names, whether a value the
 * clause names twice is one node held twice or two equal nodes, and however many levels name the
 * one below twice over.
 *
 * <p>Built from the parts rather than a source, so the question is the reading of a clause and
 * nothing that parses or types it. The deep clause is a chain the walk that meets a node once per
 * path to it would not finish: the bound is only the way a test ends, and what is held is the set.
 */
class TheFieldsAClauseReadsAreTheSameHoweverItsNodesAreSharedTest {

    private static final SourcePos POS = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    private final Hir.Binders binders = new Hir.Binders(OWNER);
    private final Core.Binder total = field("total");
    private final Core.Binder other = field("other");
    private final Map<BindingId, String> fields =
            Map.of(total.binding(), "total", other.binding(), "other");

    private Core.Binder field(String name) {
        return CoreBinders.of(binders.binder(name, POS));
    }

    private Core read(Core.Binder binder) {
        return new Core.Read(binder.name(), binder.binding(), Type.INT, POS);
    }

    private static Core sum(Core left, Core right) {
        return new Core.Binary(BinOp.ADD, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    private Set<String> readFrom(Core clause) {
        Set<String> out = new HashSet<>();
        RecordRules.readFrom(clause, fields, out);
        return out;
    }

    @Test
    void aDeepSharedClauseReadsTheFieldsAtItsBottomAndNoOthers() {
        Core shared = sum(read(total), new Core.Int(2, Type.INT, POS));
        for (int i = 0; i < 40; i++) {
            shared = sum(shared, shared);
        }
        Core clause = shared;

        Set<String> read = assertTimeoutPreemptively(Duration.ofSeconds(30), () -> readFrom(clause));

        assertEquals(Set.of("total"), read);
    }

    @Test
    void aSharedClauseReadsWhatTheSameClauseWithNothingSharedReads() {
        Core sharedTwice = sum(read(total), read(other));
        Core shared = sum(sharedTwice, sharedTwice);
        Core unshared = sum(sum(read(total), read(other)), sum(read(total), read(other)));

        assertEquals(readFrom(unshared), readFrom(shared));
        assertEquals(Set.of("total", "other"), readFrom(shared));
    }

    /** What one reading met is not carried to the next: asked twice of one clause, it answers the
     *  same, so the left and the right of a comparison that share a node each read it. */
    @Test
    void aSecondReadingOfTheSameClauseFindsTheSameFields() {
        Core node = read(total);
        Core clause = sum(node, node);

        assertEquals(Set.of("total"), readFrom(clause));
        assertEquals(Set.of("total"), readFrom(clause));
    }

    @Test
    void aClauseReadingNoFieldReadsNone() {
        Core constant = new Core.Int(2, Type.INT, POS);
        assertEquals(Set.of(), readFrom(sum(constant, constant)));
    }
}
