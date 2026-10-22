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
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;

/**
 * What a search down a tree ({@link RecursionOverATree}) collects into the list it answers, read off
 * its body: the entries of an input map that the key of each node it reaches names, and the nodes
 * below through the fields it goes down.
 *
 * <p>By induction over the tree. The body answers, from a node, the entry its own key names — or
 * nothing where the map holds none — and what the search answers from each node in a list of nodes
 * of the node, once each, put end to end. Then what the search answers from the root is the entry
 * of every node from the root down, and so is the same set of entries whatever order and however
 * deep. A body that collects anything else, or goes below a field twice, or skips a field the
 * search goes down elsewhere, is not read so.
 *
 * <p>The reading evaluates the body abstractly. A value is one of: the entry a lookup found, an
 * optional of it, a list whose elements are such entries and the lists of the nodes below, or an
 * optional of such a list. The operations it follows are the ones whose laws say where their
 * elements come from: a list of one value or none, putting two lists end to end, an optional's
 * closure applied to what it holds, a lookup of a key in a map, a match on an optional and a walk
 * from a seed over a field of the node that puts each call of the search on the elements of that
 * field to the end of what it carried.
 */
final class CollectedBelowATree {

    /**
     * What the search collects.
     *
     * @param root    where the node the search starts from stands
     * @param through the fields of a node the search goes down, each once
     * @param map     the map whose entries are collected
     * @param keyAt   the fields from a node to the key its entry is looked up by
     */
    record Collected(TermPath root, List<String> through, TermPath map, List<String> keyAt) {}

    private CollectedBelowATree() {}

    /**
     * What the search that {@code recursion} is, called with {@code args} where {@code reads}
     * stands, collects — or null where its body is not read as collecting entries of one map by the
     * key of each node.
     */
    static Collected of(InputReads reads, List<Core> args, ARecursion recursion, Symbols symbols,
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
        if (!(body.eval(recursion.body().body(), inside, Map.of()) instanceof Abs.Elems elems)
                || !elems.entries() || elems.children().isEmpty() || body.map == null
                || body.map.isAtOrUnder(root) || root.isAtOrUnder(body.map)
                || body.keyAt.isEmpty() || elems.children().contains(body.keyAt.getFirst())) {
            return null;
        }
        return new Collected(root, List.copyOf(elems.children()), body.map, body.keyAt);
    }

    /** What a value in the body stands for. */
    private sealed interface Abs {

        /** The entry a lookup found. */
        record Entry() implements Abs {}

        /** What a lookup answers: the entry, or nothing. */
        record MaybeEntry() implements Abs {}

        /** A list of the entries of nodes and of the lists the nodes below answer. */
        record Elems(boolean entries, Set<String> children) implements Abs {

            public Elems {
                children = new TreeSet<>(children);
            }

            /** Two lists put end to end, or null where some field would be gone down twice. */
            Elems with(Elems other) {
                Set<String> both = new TreeSet<>(children);
                for (String field : other.children) {
                    if (!both.add(field)) {
                        return null;
                    }
                }
                return new Elems(entries || other.entries, both);
            }
        }

        /** An optional of such a list. */
        record MaybeList(Elems of) implements Abs {}
    }

    private static final class Reading {

        private final RecursionOverATree search;
        private final TermPath root;
        private final Symbols symbols;
        private final DeclarationNewtypes newtypes;
        private TermPath map;
        private List<String> keyAt = List.of();

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

        /** What {@code core} stands for, read where {@code at} stands, or null where it is none
         *  of the values above. */
        Abs eval(Core core, InputReads at, Map<BindingId, Abs> env) {
            Denotation stands = at.standing(core, symbols, newtypes);
            Core e = Core.withoutStanding(stands.value());
            InputReads here = stands.at();
            return switch (e) {
                case Core.Read read -> env.get(read.binding());
                case Core.ListLit list -> list.elements().isEmpty()
                        ? new Abs.Elems(false, Set.of())
                        : list.elements().size() == 1
                                && eval(list.elements().getFirst(), here, env) instanceof Abs.Entry
                                ? new Abs.Elems(true, Set.of()) : null;
                case Core.Match match -> evalMatch(match, here, env);
                default -> evalOperation(e, here, env);
            };
        }

        private Abs evalOperation(Core e, InputReads here, Map<BindingId, Abs> env) {
            SeededWalk walk = SeededWalk.of(e, blocksAt(here));
            if (walk != null) {
                return evalWalk(walk, here, env);
            }
            if (!(AnOperationApplied.of(e) instanceof AnOperationApplied(ValueName operation,
                                                                          List<Core> args))) {
                return null;
            }
            if (operation.equals(ValueName.Stdlib.operation("List", "append"))) {
                return eval(args.get(0), here, env) instanceof Abs.Elems left
                        && eval(args.get(1), here, env) instanceof Abs.Elems right
                        ? left.with(right) : null;
            }
            if (operation.equals(ValueName.Stdlib.operation("Map", "get"))) {
                return lookup(args.get(0), args.get(1), here) ? new Abs.MaybeEntry() : null;
            }
            if (operation.equals(ValueName.Stdlib.operation("Option", "map"))) {
                Core.Block closure = blocksAt(here).apply(args.get(0));
                if (closure == null || closure.params().size() != 1
                        || closure.params().getFirst().binding() == null
                        || !(eval(args.get(1), here, env) instanceof Abs.MaybeEntry)) {
                    return null;
                }
                Map<BindingId, Abs> inside = new HashMap<>(env);
                inside.put(closure.params().getFirst().binding(), new Abs.Entry());
                return eval(closure.body(), here, inside) instanceof Abs.Elems elems
                        ? new Abs.MaybeList(elems) : null;
            }
            return null;
        }

        /** Whether the lookup of {@code key} in {@code from} is the one entry each node collects:
         *  the key a field chain of the node, the map a position apart from the tree, and both the
         *  same at every node. */
        private boolean lookup(Core key, Core from, InputReads here) {
            if (!(here.pathOf(key, newtypes) instanceof PathResolution.At(TermPath keyed))
                    || !(here.pathOf(from, newtypes) instanceof PathResolution.At(TermPath in))
                    || !keyed.isAtOrUnder(root) || keyed.equals(root)) {
                return false;
            }
            List<String> fields = new ArrayList<>();
            for (TermPath.Step step : keyed.steps().subList(root.steps().size(),
                    keyed.steps().size())) {
                if (!(step instanceof TermPath.Step.Field(String name))) {
                    return false;
                }
                fields.add(name);
            }
            if (map != null && (!map.equals(in) || !keyAt.equals(fields))) {
                return false;
            }
            map = in;
            keyAt = List.copyOf(fields);
            return true;
        }

        /**
         * A match on what a lookup answered, whose arms are one or the other and never both: the
         * arm with what it holds where there is something, the other where there is not.
         *
         * <p>So it is no two lists put end to end. Each arm is read on its own — the first with its
         * name standing for what the lookup's optional holds — and the match answers one value
         * either way only where both go down the same fields of the node and only the first holds
         * the entry: it is then the entry where the node has one, and the same lists below
         * whichever. An arm going down fields the other does not would collect below some nodes
         * and not others, which no one value of every node is, and is not read.
         */
        private Abs evalMatch(Core.Match match, InputReads here, Map<BindingId, Abs> env) {
            if (!(eval(match.scrutinee(), here, env) instanceof Abs.MaybeList maybe)
                    || match.cases().size() != 2) {
                return null;
            }
            Abs.Elems present = null;
            Abs.Elems absent = null;
            for (Core.Case arm : match.cases()) {
                if (arm.binding() instanceof Core.ArmBinding.Payload payload) {
                    if (present != null || payload.binder() == null
                            || payload.binder().binding() == null) {
                        return null;
                    }
                    Map<BindingId, Abs> holding = new HashMap<>(env);
                    holding.put(payload.binder().binding(), maybe.of());
                    if (!(eval(arm.body(), here, holding) instanceof Abs.Elems some)) {
                        return null;
                    }
                    present = some;
                } else {
                    if (absent != null || !(eval(arm.body(), here, env) instanceof Abs.Elems none)) {
                        return null;
                    }
                    absent = none;
                }
            }
            return present == null || absent == null || absent.entries()
                    || !present.children().equals(absent.children()) ? null : present;
        }

        /** A walk from a seed over a field of the node whose step puts the search from each
         *  element of that field to the end of what it carried. */
        private Abs evalWalk(SeededWalk walk, InputReads here, Map<BindingId, Abs> env) {
            if (!(here.pathOf(walk.container(), newtypes) instanceof PathResolution.At(
                    TermPath over)) || over.steps().size() != root.steps().size() + 1
                    || !over.isAtOrUnder(root)
                    || !(over.steps().getLast() instanceof TermPath.Step.Field(String field))
                    || !(eval(walk.seed(), here, env) instanceof Abs.Elems seed)
                    || !stepsDownOnEachElement(walk, here)) {
                return null;
            }
            return seed.with(new Abs.Elems(false, Set.of(field)));
        }

        /** Whether the step is what was carried put before the search from the element. */
        private boolean stepsDownOnEachElement(SeededWalk walk, InputReads here) {
            Denotation step = here.standing(walk.step().body(), symbols, newtypes);
            if (!(AnOperationApplied.of(Core.withoutStanding(step.value()))
                    instanceof AnOperationApplied(ValueName operation, List<Core> args))
                    || !operation.equals(ValueName.Stdlib.operation("List", "append"))) {
                return false;
            }
            Set<Core> operands = new LinkedHashSet<>();
            boolean carried = false;
            boolean descends = false;
            for (Core written : args) {
                Core each = Core.withoutStanding(written);
                if (!operands.add(each)) {
                    continue;
                }
                if (each instanceof Core.Read read
                        && read.binding().equals(walk.accumulator().binding())) {
                    carried = true;
                } else if (each instanceof Core.Call call && search.again().contains(call)
                        && Core.withoutStanding(call.args().get(search.node()))
                                instanceof Core.Read element
                        && element.binding().equals(walk.element().binding())) {
                    descends = true;
                }
            }
            return carried && descends && operands.size() == 2;
        }
    }
}
