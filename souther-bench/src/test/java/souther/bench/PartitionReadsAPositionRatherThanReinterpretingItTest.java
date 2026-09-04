package souther.bench;

import org.junit.jupiter.api.Test;

import souther.bench.PositionReadings.Authority;
import souther.bench.PositionReadings.Traversal;

import java.io.IOException;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The partitioning stage reads what a position is; it never works it out again underneath.
 *
 * <p>What a value is made of has one answer, and the stage had it four ways over: from the reading
 * of a position, from the declaration through its field types, from a collection constructor taken
 * apart by hand, and from a walk reaching through the names a value is written under. Four readings
 * of one fact agree wherever they happen to stop at the same depth and part everywhere else — at a
 * sum, at a name over a name, inside a container — and each parting was a defect found separately.
 *
 * <p><b>So this is about reachability and not about a vocabulary.</b> A rule naming the ways
 * anybody had written it down so far would be passed by the next one written another way, and that
 * is the failure this exists after rather than a hypothetical: the walk it removed reached the
 * declaration through an accessor no earlier rule watched. What is checked is that no path from the
 * stage arrives at raw structure at all, however many methods it goes through and whatever those
 * methods return. A helper handing back a {@code boolean} hides nothing here, because what is
 * followed is the call and not the answer.
 *
 * <p><b>What counts as raw structure is the types' own statement.</b> {@link
 * souther.compiler.types.Type.Leaf} says it holds no type inside it and {@link
 * souther.compiler.types.Type.Compound} says it is built out of others, so taking a compound apart
 * is reading structure and reading the name off a {@code Ref} is not — a {@code Ref} has no
 * structure to read, which is what makes it a leaf. {@link souther.compiler.ast.Hir.Def} permits
 * the declarations, so reaching one of those is reading what a module wrote. Both sets are derived
 * from the sealed hierarchies rather than listed here, and a constructor added to either joins them
 * without anybody remembering to.
 *
 * <p><b>The table is of authorities, and that is the point.</b> Each is a place that owns a
 * question, reads whatever raw material that question needs, and hands back an answer. It is not a
 * list of methods allowed past the boundary — it is why the stage does not need to look past it. A
 * method reaching raw structure that no authority answers for is a second reading of something
 * already decided, whatever it is called.
 *
 * <p>What the walk itself does is held by {@link ThisReadingSeesAReadingOfRawStructureTest}, which
 * hands it code written to be read. Green here says the compiler is clean; green there says this
 * would have gone red had it not been.
 */
class PartitionReadsAPositionRatherThanReinterpretingItTest {

    /**
     * Why the stage does not have to look past each of these.
     *
     * <p>A place earns an entry by answering four things. It has a question of its own, rather than
     * giving another authority's answer a second name. What it hands back is that answer, never the
     * raw material — a type as the subject of a question is fine, a child type or a declaration
     * handed out is not. It finishes before anything of the caller's runs. And it is the lowest
     * owner: a facade or a switch that hands the decision on is walked through to whatever makes
     * it.
     */
    private static final List<Authority> AUTHORITIES = List.of(
            // What a position is, and how it is written. The one this stage stands on.
            new Authority("what a position is, with the names it is written under off",
                    "souther.compiler.check.TypeView", Traversal.OPAQUE),
            new Authority("what the rules written on a record leave its fields able to hold",
                    "souther.compiler.check.FieldDomains", Traversal.OPAQUE),
            new Authority("which conjuncts are written on each of the names a value wears",
                    "souther.compiler.check.DeclaredClauses", Traversal.OPAQUE),
            new Authority("which ends a declaration writes on the values of a type",
                    "souther.compiler.check.DeclaredBounds", Traversal.OPAQUE),
            new Authority("which binding each field of a declaration introduces inside its own"
                            + " invariant",
                    "souther.compiler.check.TypeOps#fieldBindings", Traversal.OPAQUE),
            new Authority("what carries the values of a type, and in what order",
                    "souther.compiler.check.Carrier", Traversal.OPAQUE),
            new Authority("whether reading a field reaches another location",
                    "souther.compiler.check.Location", Traversal.OPAQUE),
            new Authority("what there is to count about a value",
                    "souther.compiler.check.NumericMeasures", Traversal.OPAQUE),
            new Authority("which distinctions the type at a position states",
                    "souther.compiler.inputs.Distinctions", Traversal.OPAQUE),
            new Authority("what reaches each position of a behavior's inputs, read once",
                    "souther.compiler.inputs.InputDomain", Traversal.OPAQUE),
            new Authority("what a name in the tree denotes where the reader stands",
                    "souther.compiler.inputs.InputReads", Traversal.OPAQUE),
            new Authority("which number of an input an expression names",
                    "souther.compiler.inputs.InputNumber", Traversal.OPAQUE),
            new Authority("which number a comparison draws which line on",
                    "souther.compiler.inputs.ComparedNumber", Traversal.OPAQUE),
            new Authority("whether an operation and a position make one term of a number taken of"
                            + " a value",
                    "souther.compiler.inputs.NumericTerm$TakenOf", Traversal.OPAQUE),
            new Authority("how a type is written where an author reads it",
                    "souther.compiler.types.Type#show", Traversal.OPAQUE),

            // Owners all the same, walked through. Neither can stand as a boundary: what one
            // answers with is composed by a reading the caller wrote, and the other hands its
            // decision to whichever term it is about — so a stop at either would leave the walk
            // this checks on the far side of it.
            new Authority("what affine form an expression composes",
                    "souther.compiler.check.AffineForms", Traversal.TRANSPARENT),
            new Authority("what a term about a number comes to at another position",
                    "souther.compiler.inputs.NumericTerm", Traversal.TRANSPARENT));

    private static PositionReadings.Over thisCompiler() throws IOException {
        return new PositionReadings.Over(Reactor.classes(), "souther.compiler.partition.",
                "souther.compiler.ast.Hir$Def", "souther.compiler.check.Symbols#declaredNode",
                "souther.compiler.types.Type$Compound", "Lsouther/compiler/types/Type;",
                AUTHORITIES);
    }

    /**
     * No path from the stage reaches raw structure without an authority answering for it.
     *
     * <p>Both what a method's own code does and what it calls, to any depth. A place that reads
     * structure and hands back a word about it is on the path like any other: what makes the
     * difference is whether some authority owns the question, not what the answer is made of.
     */
    @Test
    void nothingInTheStageReadsStructureThatNoAuthorityAnswersFor() throws IOException {
        PositionReadings.Over over = thisCompiler();
        PositionReadings.Reading read = PositionReadings.of(over);

        assertFalse(read.observers().isEmpty(),
                "no reading of raw structure was found anywhere, so this asserts nothing about the"
                        + " stage: the walk or the sums it derives from are wrong rather than the"
                        + " compiler clean");
        assertFalse(read.inTheStage().isEmpty(),
                "the stage has no compiled methods, so nothing was checked");

        assertEquals(List.of(), read.bypasses(),
                "a path from the partitioning stage to raw structure that no authority answers"
                        + " for. Either the question it is asking has an owner and it should ask"
                        + " there, or it is a second reading of something a reading already"
                        + " decided");
    }

    /**
     * Every authority is one the stage actually reaches.
     *
     * <p>The other way round, and the half that keeps this from becoming a list. An entry nothing
     * arrives at is a rule about a boundary that is not there — either the reader that needed it
     * has gone, and the entry with it, or the walk stopped reaching it and what this checks has
     * quietly narrowed.
     */
    @Test
    void everyAuthorityIsOneTheStageArrivesAt() throws IOException {
        PositionReadings.Over over = thisCompiler();
        assertEquals(List.of(), PositionReadings.unreached(over, PositionReadings.of(over)),
                "an authority nothing in the stage arrives at, which is a rule about a boundary"
                        + " that is not there");
    }
}
