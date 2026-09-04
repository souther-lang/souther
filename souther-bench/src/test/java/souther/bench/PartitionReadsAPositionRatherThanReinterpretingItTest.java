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
 * <p>Over the calls as written, which is the shape of what this claims. A method reached only
 * through an interface has no edge here, so a seam of that kind is held by what is on the far side
 * of it being in the stage rather than by this. Every reading the stage has today is reached
 * through a class a call names.
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
            new Authority("which ends a declaration writes on the values of a type, and how much"
                            + " they say it holds",
                    "souther.compiler.check.DeclaredBounds", Traversal.OPAQUE),
            new Authority("which conjuncts are written on each of the names a value wears",
                    "souther.compiler.check.DeclaredClauses", Traversal.OPAQUE),
            new Authority("what carries the values of a type, and in what order",
                    "souther.compiler.check.Carrier", Traversal.OPAQUE),
            new Authority("whether reading a field reaches another location",
                    "souther.compiler.check.Location", Traversal.OPAQUE),
            new Authority("what there is to count about a value",
                    "souther.compiler.check.NumericMeasures", Traversal.OPAQUE),
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

            // Named by the operation, because the class holds more than one question. A second
            // operation beside these, about something else, would be answering under a name that
            // was never about it — which is what naming the class would let it do.
            new Authority("which distinctions the type at a position states",
                    "souther.compiler.inputs.Distinctions#ofType", Traversal.OPAQUE),
            new Authority("which binding each field of a declaration introduces inside its own"
                            + " invariant",
                    "souther.compiler.check.TypeOps#fieldBindings", Traversal.OPAQUE),
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

    static PositionReadings.Over thisCompiler() throws IOException {
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
     * The table names exactly the operations that have to be answered for.
     *
     * <p>Both ways round, and derived rather than judged. What needs an answer is worked out by
     * running the same walk with nothing answering: every operation the stage calls that would
     * arrive at raw structure on its own. An operation missing from the table has nobody saying
     * what question it answers; an entry that answers for nothing is a rule about a boundary that
     * is not there.
     *
     * <p>Which is also what keeps a boundary the size of its question. Named by its class, an
     * authority answers for whatever else that class comes to hold — a second operation beside it,
     * about something else, reaching the declarations under a question that was never about them.
     * Named by the operation, that second one arrives here instead.
     */
    @Test
    void theTableNamesTheOperationsThatHaveToBeAnsweredFor() throws IOException {
        PositionReadings.Over over = thisCompiler();
        PositionReadings.Reading read = PositionReadings.of(over);

        List<String> unanswered = read.answering().stream()
                .filter(each -> AUTHORITIES.stream().noneMatch(one -> one.answersFor(each)))
                .sorted().toList();
        List<String> answersForNothing = AUTHORITIES.stream()
                .filter(one -> read.answering().stream().noneMatch(one::answersFor))
                .map(Authority::owns).sorted().toList();

        assertEquals(List.of(), unanswered,
                "an operation the stage calls that reaches raw structure and nothing says what"
                        + " question it answers");
        assertEquals(List.of(), answersForNothing,
                "an entry answering for nothing the stage calls, which is a rule about a boundary"
                        + " that is not there");
    }

    /**
     * A case of what is built out of types is one this can read the components of.
     *
     * <p>Which components hold a type is read off the record attribute, so a case that is not a
     * record holds nothing this can see, and a walk taking it apart would read as taking nothing
     * apart. The claim that a case added to the sum joins the rule without anybody remembering to
     * holds exactly as far as this does.
     */
    @Test
    void everythingBuiltOutOfTypesIsOneThisCanReadTheComponentsOf() throws IOException {
        assertEquals(List.of(), PositionReadings.of(thisCompiler()).madeOfNonRecords(),
                "a case of what is built out of types that is not a record: what it holds is not"
                        + " where this reads what a compound holds, so taking it apart would read"
                        + " as reading nothing");
    }
}
