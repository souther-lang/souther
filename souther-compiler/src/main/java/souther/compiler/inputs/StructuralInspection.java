package souther.compiler.inputs;

import souther.compiler.check.Shape;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Whether a position stands once what is under it has been read, and how the reading goes on from
 * it.
 *
 * <p><b>A continuation and not a classifier.</b> The derivation reads what a position's own type
 * says first — the classes it divides into, the ends its rules put on it — and only where that says
 * nothing does it ask what is under the position. So this is reached after local evidence is
 * exhausted, never instead of it, and an answer here says nothing about what the local reading
 * found. A sum answers {@link Retained} with branches under it, and a sum is the position most
 * likely to have had classes: the answer means the sum is not made of positions, not that nothing
 * divides it.
 *
 * <p><b>Two answers, and the difference between them is what becomes of the position.</b> A
 * {@link Decomposed} position is given up in favour of what is under it: a record states no
 * distinction of its own and carries no end, so nothing is read there that a reader would have to
 * weigh against its fields. Everything else is {@link Retained} — the position stands, whatever the
 * reading goes on to do below it.
 *
 * <p><b>Retained is not an absence, and neither is any continuation of one.</b> Whether the position
 * divides is still open when one comes back, because the rules a behavior's body writes have not
 * been read yet — a bare {@code List<String>} nothing bounds continues into its elements and is
 * still undivided until a {@code guard List.length(t.names) > 0} draws a line on it, and a
 * {@link Continuation.Blocked} is the reason the position would be left with if nothing else
 * answered for it rather than a verdict. Nothing here may be turned into a report of a position the
 * model does not divide; that conclusion needs the phases after this one to have finished too.
 */
public sealed interface StructuralInspection {

    /**
     * The position is made of these, each of which is read the same way — in the order the
     * declaration writes them, which is the order they are walked and reported in.
     *
     * <p>The descent's answer as it stands, rather than the fields taken out of it and put into a
     * value of this reading's own. What is under a type is {@link StructuralDescent}'s to say, and
     * unpacking its answer to repackage it leaves two values of one fact where the point of asking
     * one owner was to have one.
     */
    record Decomposed(StructuralDescent.Children descent) implements StructuralInspection {

        /** The fields, as the descent answered them. */
        public Map<String, Type> under() {
            return descent.under();
        }
    }

    /**
     * The position stands, and this is how the reading goes on from it.
     *
     * <p>The one thing every arm of {@link Continuation} has in common, said once. A reader deciding
     * what becomes of the position asks that here and asks the continuation nothing; a reader
     * walking on asks the continuation and does not have to know that the position survived.
     */
    record Retained(Continuation continuation) implements StructuralInspection {

        public Retained {
            if (continuation == null) {
                throw new IllegalArgumentException(
                        "a position that stands with no account of what follows it");
            }
        }
    }

    /** How a reading goes on from a position that stands. */
    sealed interface Continuation {

        /**
         * Nothing follows the position.
         *
         * <p>Says that and only that. Whether it divides is still open — the rules a body writes
         * have not been read — so this is a position still to be answered for, and what it becomes
         * if nothing answers is an absence. Reading it as one here puts back the defect the protocol
         * removes.
         */
        record None() implements Continuation {}

        /**
         * The position holds values of {@code element}, each of which is read the same way, at the
         * one position they share.
         *
         * <p>One position for however many the list holds, and the path says no more than that
         * ({@link TermPath.Step.Element}). What is written about the elements is written once, so
         * what is read of them is read once; how many of them a row has to put in a class is settled
         * where the class is and not here.
         *
         * @param element what the sequence holds, as the signature wrote it
         */
        record Elements(Type element) implements Continuation {}

        /**
         * The position is one of these, and each of them continues differently.
         *
         * <p>The one continuation that is conditional. A field of a record is under the record
         * whatever the row holds; a field of a case is under the position only where the value
         * there turned out to be that case, and what says so is the {@link Refinement} the branch
         * carries — which a path writes down and every reader of one derives its requirements from.
         *
         * <p><b>What the type structurally has, and not what a behavior is owed.</b> A branch a
         * behavior's rules leave nothing at is still a branch of the type. Which of these the
         * reading of one input goes down is that reading's to settle ({@link InputDomain}), from
         * the obligations the position came back with — asked here, this would be answering about a
         * behavior from a fact about a declaration.
         */
        record Branches(List<Branch> branches) implements Continuation {

            public Branches {
                branches = List.copyOf(branches);
            }
        }

        /**
         * The continuation under the position was not made, and why.
         *
         * <p>Not one reason but three kinds of reason, and they are not the same claim about the
         * model. A traversal this compiler cannot express and a type it could not interpret say
         * something about what is there; a {@link BlockReason.DepthLimit} says only that <em>this
         * reader</em> stopped here, and a reader that goes further finds the positions it declined
         * to look at. Read as "the model puts nothing reachable under this position", the third is a
         * claim nobody made — and it is the one that had a second walk built beside this one,
         * because everything past the reading's depth looked unreachable rather than unasked.
         *
         * <p>{@code why} is the reason this position is left with if nothing else answers for it,
         * not a verdict. A rule a body writes may still draw a line on this same position — a
         * length, a size — and where one does, that is what the position is measured at and this
         * reason is never reported. What it does not do is let a rule about what is <em>inside</em>
         * stand in for reaching inside.
         */
        record Blocked(BlockReason.AboutThePosition why) implements Continuation {}
    }

    /**
     * One way the value at a position can turn out, and what stands under it when it does.
     *
     * <p>A branch exists whether or not anything stands under it, and the two are kept apart
     * because they are not the same fact: a unit case is a branch of its sum and puts no position
     * anywhere, and reading "no continuation" as "no branch" would take the case out of what a row
     * is owed at the position above.
     *
     * @param refinement what the value turned out to be, which is what a path under this branch
     *                   writes and what a row there has to meet
     * @param under      what stands at the narrowed position, or null where the branch is the whole
     *                   of a value and nothing stands under it. Not a step inward: what a case of a
     *                   sum holds is the value the sum held, so this is the type at the same
     *                   position and not the type of something inside it
     */
    record Branch(Refinement refinement, Type under) {

        public Branch {
            if (refinement == null) {
                throw new IllegalArgumentException("a branch that narrows nothing is not one");
            }
        }
    }

    /**
     * What follows {@code shape}, or why nothing can.
     *
     * <p>Exhaustive over the shapes a position can have, with no {@code default}. Every one is
     * answered here, so a shape admitted later is a compile error rather than a position that
     * quietly has nothing under it.
     *
     * @param shape    the position's shape, already proved to be one a partition is derived from
     * @param deeper   whether this reading goes on down, which only a position made of positions can
     *                 be stopped by. The reading's own answer and not the type's: how far a report is
     *                 about one input is what it settles, and a reader that wants what is under a
     *                 position this stopped at asks {@link StructuralDescent} rather than being told
     *                 there is nothing there
     * @param declared the distinctions the position's type states, as the one reading of them
     *                 answered ({@link Distinctions#ofType}). Handed in rather than read again: what
     *                 a sum's cases are is one fact, and a second reading of it here would be the
     *                 branches and the classes disagreeing about which cases a position has
     */
    static StructuralInspection of(Shape.ReadablePositionShape shape, boolean deeper,
                                   List<Case> declared) {
        return switch (shape) {
            // Made of positions, and read one level down — unless this reading stops here, which is
            // a reading that declines to look rather than a record with nothing in it.
            case Shape.Product product -> deeper
                    ? new Decomposed(StructuralDescent.of(product))
                    : stopped(new BlockReason.DepthLimit());
            // What a sequence holds is one position, reached whether or not this reading stops
            // here — and the sequence goes on standing either way, since its own length is a number
            // rules are written about.
            case Shape.Sequence sequence -> deeper
                    ? new Retained(new Continuation.Elements(sequence.element()))
                    : stopped(new BlockReason.DepthLimit());
            // The sum stands and each of its cases continues on its own. Not made of positions:
            // what a case declares is under the case and not under the sum, which is why this is a
            // continuation rather than a decomposition, and why the sum keeps the classes it has.
            case Shape.Sum _ -> new Retained(new Continuation.Branches(branchesOf(declared)));
            // Still held inside something nothing here reaches into. A branch under one is exactly
            // what would lift it — whether the optional holds anything is a narrowing like any
            // other — and it is not taken here.
            case Shape.Optional _ -> stopped(new BlockReason.UnsupportedTraversal(
                    BlockReason.Traversal.OPTIONAL_VALUE));
            case Shape.Mapping _ -> stopped(new BlockReason.UnsupportedTraversal(
                    BlockReason.Traversal.MAPPING_CONTENT));
            // Nothing was interpreted, so there is nothing to be made of. A model carrying one
            // compiles, which is why this is answered rather than refused.
            case Shape.Unresolved _ -> stopped(new BlockReason.TypeUnresolved());
            // Nothing follows. A value of one of these is one value — which is a different
            // statement from the position having no classes, and this makes neither.
            case Shape.Scalar _, Shape.Unit _ -> new Retained(new Continuation.None());
        };
    }

    private static StructuralInspection stopped(BlockReason.AboutThePosition why) {
        return new Retained(new Continuation.Blocked(why));
    }

    /**
     * The branches of a sum, from the cases its type states.
     *
     * <p>Whether a case is the whole of a value is read off the distinction that already answered
     * it ({@link Case.SumCase#oneValue}), so that what a row is owed at the position and what
     * stands under the case are crossed against one reading of the declaration.
     */
    private static List<Branch> branchesOf(List<Case> declared) {
        List<Branch> out = new ArrayList<>();
        for (Case each : declared) {
            // A sum states its cases and nothing else. Anything else in this list is the reading of
            // distinctions and the reading of structure disagreeing about what a sum is, which is
            // left to say itself rather than turned into a branch of some other kind.
            if (each instanceof Case.SumCase one) {
                out.add(new Branch(new Refinement.SumCase(one.leaf()),
                        one.oneValue() ? null : Type.ref(one.leaf())));
            }
        }
        return List.copyOf(out);
    }
}
