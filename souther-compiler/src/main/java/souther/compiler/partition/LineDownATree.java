package souther.compiler.partition;

import souther.compiler.check.ARecursion;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.RecursionOverATree;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WrittenOfANode;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * The line of nodes a search down a tree ({@link RecursionOverATree}) answers, read off its body:
 * from the node it is handed to the first node, in the order it goes down, whose value at some
 * fields is the value it is handed beside the node — or nothing where no node has it.
 *
 * <p>By induction over the tree. The body answers a list of the node alone where the node holds
 * the value, and otherwise what a walk from nothing over the elements of one field of the node
 * answers, with the node put before it: the walk keeps the answer of the first element whose search
 * answered something, and the search it makes from each element is this one. Then what the search
 * answers from a node is the node and the nodes down to the first one holding the value, the root
 * of that line first, or nothing where no node below holds it. A body that puts anything else in the
 * list, goes down more than one field, or asks anything but that one equality of the node, is not
 * read so.
 *
 * <p>The reading evaluates the body abstractly. A value is one of: nothing, a list of one value,
 * what the walk answers (the line below some element, or nothing), and the line from the node.
 */
final class LineDownATree {

    /**
     * What the search answers.
     *
     * @param root    where the node the search starts from stands
     * @param through the field of a node whose elements it goes down
     * @param matchAt the fields from a node to the value it holds that is compared
     * @param key     where the value it is compared with stands
     * @param matched the type of the two values compared
     */
    record Line(TermPath root, String through, List<String> matchAt, TermPath key, Type matched) {}

    private LineDownATree() {}

    /**
     * The line that the search that {@code recursion} is, called with {@code args} where
     * {@code reads} stands, answers — or null where its body is not read as one.
     */
    static Line of(InputReads reads, List<Core> args, ARecursion recursion, Symbols symbols,
                   DeclarationNewtypes newtypes) {
        RecursionOverATree search = recursion.search().orElse(null);
        if (search == null || !(reads.pathOf(args.get(search.node()), newtypes)
                instanceof PathResolution.At(TermPath root)) || !RunSource.oneTreeStandsAt(root)) {
            return null;
        }
        for (int at = 0; at < args.size(); at++) {
            if (at != search.node() && !(reads.pathOf(args.get(at), newtypes)
                    instanceof PathResolution.At(TermPath stays)
                    && WrittenOfANode.apart(stays, root))) {
                return null;
            }
        }
        InputReads inside = reads.searching(recursion.body(), args, newtypes);
        if (inside == null) {
            return null;
        }
        Reading body = new Reading(search, root, symbols, newtypes);
        Denotation stands = inside.standing(recursion.body().body(), symbols, newtypes);
        if (!(Core.withoutStanding(stands.value()) instanceof Core.If fork)
                || !body.holdsTheValue(fork.cond(), stands.at())
                || !(body.eval(fork.then(), stands.at(), Map.of()) instanceof Abs.One)
                || !(body.eval(fork.els(), stands.at(), Map.of()) instanceof Abs.Line below)
                || body.matchAt == null || below.field() == null) {
            return null;
        }
        return new Line(root, below.field(), body.matchAt, body.key, body.matched);
    }

    /** What a value in the body stands for. */
    private sealed interface Abs {

        /** A list of nothing. */
        record Nothing() implements Abs {}

        /** A list of one value, which is the node. */
        record One() implements Abs {}

        /** What the walk over the elements of {@code field} answers: the line below the first
         *  element that has one, or nothing. */
        record Below(String field) implements Abs {}

        /** The node put before what the walk over {@code field} answers, or nothing where the
         *  walk answered nothing. */
        record Line(String field) implements Abs {}
    }

    private static final class Reading {

        private static final ValueName.Stdlib.Operation IS_EMPTY =
                ValueName.Stdlib.operation("List", "isEmpty");
        private static final ValueName.Stdlib.Operation APPEND =
                ValueName.Stdlib.operation("List", "append");

        private final RecursionOverATree search;
        private final TermPath root;
        private final Symbols symbols;
        private final DeclarationNewtypes newtypes;
        private List<String> matchAt;
        private TermPath key;
        private Type matched;

        Reading(RecursionOverATree search, TermPath root, Symbols symbols,
                DeclarationNewtypes newtypes) {
            this.search = search;
            this.root = root;
            this.symbols = symbols;
            this.newtypes = newtypes;
        }

        private Function<Core, Core.Block> blocksAt(InputReads at) {
            return closure -> Core.withoutStanding(at.standing(closure, symbols, newtypes).value())
                    instanceof Core.Block block ? block : null;
        }

        /**
         * Whether {@code cond} asks whether a field of the node is the value handed beside it, and
         * nothing else: an equality of two values as they stand, one a chain of fields from the
         * node and the other a place apart from the tree.
         */
        boolean holdsTheValue(Core cond, InputReads at) {
            if (!(Core.withoutStanding(at.standing(cond, symbols, newtypes).value())
                    instanceof Core.Binary equality) || equality.op() != BinOp.EQ
                    || !(equality.reading() instanceof Core.BinaryReading.AsTheyStand
                            || equality.reading() instanceof Core.BinaryReading.Opened)) {
                return false;
            }
            return sides(equality.left(), equality.right(), at)
                    || sides(equality.right(), equality.left(), at);
        }

        private boolean sides(Core ofTheNode, Core handed, InputReads at) {
            if (!(at.pathOf(ofTheNode, newtypes) instanceof PathResolution.At(TermPath held))
                    || !(at.pathOf(handed, newtypes) instanceof PathResolution.At(TermPath sought))
                    || !held.isAtOrUnder(root) || held.equals(root)
                    || !WrittenOfANode.apart(sought, root)) {
                return false;
            }
            List<String> fields = new ArrayList<>();
            for (TermPath.Step step : held.steps().subList(root.steps().size(),
                    held.steps().size())) {
                if (!(step instanceof TermPath.Step.Field(String name))) {
                    return false;
                }
                fields.add(name);
            }
            matchAt = List.copyOf(fields);
            key = sought;
            matched = ofTheNode.type();
            return true;
        }

        /** What {@code core} stands for, read where {@code at} stands, or null where it is none
         *  of the values above. */
        Abs eval(Core core, InputReads at, Map<BindingId, Abs> env) {
            Denotation stands = at.standing(core, symbols, newtypes);
            Core e = Core.withoutStanding(stands.value());
            InputReads here = stands.at();
            return switch (e) {
                case Core.Read read -> env.get(read.binding());
                case Core.ListLit list -> list.elements().isEmpty() ? new Abs.Nothing()
                        : list.elements().size() == 1 && here.pathOf(list.elements().getFirst(),
                                newtypes) instanceof PathResolution.At(TermPath held)
                                && held.isAtOrUnder(root) ? new Abs.One() : null;
                case Core.LetIn let -> {
                    Abs value = eval(let.value(), here, env);
                    if (value == null || let.binder().binding() == null) {
                        yield null;
                    }
                    Map<BindingId, Abs> inside = new HashMap<>(env);
                    inside.put(let.binder().binding(), value);
                    yield eval(let.body(), here, inside);
                }
                case Core.If fork -> evalFork(fork, here, env);
                default -> evalOperation(e, here, env);
            };
        }

        /**
         * Nothing where the walk answered nothing and the node put before it where it did not:
         * the line from the node. Both arms are read on their own, and the answer is one value
         * only where the walk they both name is the same one.
         */
        private Abs evalFork(Core.If fork, InputReads here, Map<BindingId, Abs> env) {
            if (!(AnOperationApplied.of(fork.cond())
                    instanceof AnOperationApplied(ValueName operation, List<Core> asked))
                    || !operation.equals(IS_EMPTY) || asked.size() != 1
                    || !(eval(asked.getFirst(), here, env) instanceof Abs.Below walk)
                    || !(eval(fork.then(), here, env) instanceof Abs.Nothing)) {
                return null;
            }
            return eval(fork.els(), here, env) instanceof Abs.Line line
                    && line.field().equals(walk.field()) ? line : null;
        }

        private Abs evalOperation(Core e, InputReads here, Map<BindingId, Abs> env) {
            SeededWalk walk = SeededWalk.of(e, blocksAt(here));
            if (walk != null) {
                return evalWalk(walk, here, env);
            }
            if (!(AnOperationApplied.of(e) instanceof AnOperationApplied(ValueName operation,
                                                                          List<Core> args))
                    || !operation.equals(APPEND) || args.size() != 2) {
                return null;
            }
            return eval(args.get(0), here, env) instanceof Abs.One
                    && eval(args.get(1), here, env) instanceof Abs.Below below
                    ? new Abs.Line(below.field()) : null;
        }

        /**
         * A walk from nothing over a field of the node whose step answers what it carried where
         * that is something, and otherwise the search from the element: so it answers the search
         * from the first element that has something to answer.
         */
        private Abs evalWalk(SeededWalk walk, InputReads here, Map<BindingId, Abs> env) {
            // The first node is the first in the order the elements are handed to the step, and a
            // row is read from the first element of a field to the last: a walk that says nothing
            // of its order, or hands them from the last, is a search for another node.
            if (!walk.inTheContainersOrder()
                    || !(eval(walk.seed(), here, env) instanceof Abs.Nothing)
                    || !(here.pathOf(walk.container(), newtypes) instanceof PathResolution.At(
                            TermPath over))
                    || over.steps().size() != root.steps().size() + 1
                    || !over.isAtOrUnder(root)
                    || !(over.steps().getLast() instanceof TermPath.Step.Field(String field))
                    || !keepsTheFirstAnswer(walk, here)) {
                return null;
            }
            return new Abs.Below(field);
        }

        /** Whether the step is {@code if List.isEmpty(carried) then <the search from the element>
         *  else carried}. */
        private boolean keepsTheFirstAnswer(SeededWalk walk, InputReads here) {
            Denotation step = here.standing(walk.step().body(), symbols, newtypes);
            if (!(Core.withoutStanding(step.value()) instanceof Core.If fork)
                    || !(AnOperationApplied.of(fork.cond()) instanceof AnOperationApplied(
                            ValueName operation, List<Core> asked))
                    || !operation.equals(IS_EMPTY) || asked.size() != 1
                    || !isRead(asked.getFirst(), walk.accumulator().binding())
                    || !isRead(fork.els(), walk.accumulator().binding())) {
                return false;
            }
            return Core.withoutStanding(fork.then()) instanceof Core.Call call
                    && search.again().contains(call)
                    && isRead(call.args().get(search.node()), walk.element().binding());
        }

        private static boolean isRead(Core e, BindingId binding) {
            return Core.withoutStanding(e) instanceof Core.Read read
                    && read.binding() != null && read.binding().equals(binding);
        }
    }
}
