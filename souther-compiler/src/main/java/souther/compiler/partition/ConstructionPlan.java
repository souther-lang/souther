package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.StructuralDescent;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Where a value has to be built under one parameter, and out of what.
 *
 * <p><b>Not the positions of an input.</b> What a behavior declares it takes is
 * {@link souther.compiler.inputs.InputDomain}'s, and what a row has to compose is this. The two are
 * written with the same {@link TermPath} and are about different things: this goes on until there is
 * a value to build, which is further than a report is about. So a path from here is never looked up
 * over there.
 *
 * <p>Where they do meet is how a position is named. A requirement narrowing a position is written
 * into the path here exactly as the reading writes it, so a class fixed at a position under a
 * refinement is a position this builds at under the same name. Written flat, the two would name one
 * location two ways, and a class the caller fixed would be looked for at a path this plan does not
 * have.
 *
 * <p><b>Worked out once and consumed three ways.</b> What each position may take, the search that
 * chooses one position at a time, and the composing of the chosen values back into a record were
 * three recursions over the same declarations, and the third said so — a value came back null "only
 * where the walk that collected the choices and this one disagree". Holding the positions and the
 * shape they compose back into as one value is what makes that disagreement unsayable rather than
 * something a test has to go looking for.
 */
record ConstructionPlan(Node root) {

    /** How deep a record is built. Past this a value stops being anything an author recognises as
     *  one input, and a type that refers to itself would not stop at all.
     *
     *  <p>This search's bound and nobody else's. What a report is about stops at two levels
     *  ({@link souther.compiler.inputs.InputDomain#MAX_DEPTH}), which answers a different question:
     *  a record four levels down still has to be constructed. */
    private static final int MAX_DEPTH = 8;

    /** One position of the value being built. */
    sealed interface Node permits Slot, Built, Held {

        /** Where it is. */
        TermPath at();

        /** What is built there — the declared type, unless a requirement narrowed the position, or
         *  the caller settled it before this was worked out. */
        Type type();

        /**
         * The newtype names still to put on what this node produces, outermost first.
         *
         * <p>One question of every node and three answers, because what produces the value differs.
         * A record and a collection are composed bare, so every name the position wears is still to
         * go on; a value chosen at a slot arrives already wearing whatever names its own type wears,
         * so what is left is the names the position wore before a requirement narrowed it — and
         * nothing at all where none did.
         *
         * <p>A row at a {@code data SlotN = Slot} carries {@code SlotN(Slot { ... })}, and a
         * {@code data DecisionN = Decision} narrowed to a case that wraps a number carries
         * {@code DecisionN(Special(5))}. A value composed without them is of a type the parameter
         * does not declare.
         */
        List<TypeOps.Layer> worn();
    }

    /**
     * A position the search chooses a value for.
     *
     * @param worn  {@link Node#worn}: the names the position wore before a requirement narrowed
     *              it, since what is chosen here already wears whatever names {@link #type} wears
     * @param fixed whether the caller had already fixed a value here, which is what says a class is
     *              being placed under whatever holds it
     */
    record Slot(TermPath at, Type type, List<TypeOps.Layer> worn, boolean fixed) implements Node {

        Slot {
            worn = List.copyOf(worn);
        }
    }

    /**
     * A sequence composed out of what stands at its element.
     *
     * <p>Only where a class is to be put there. A list nothing is being placed inside is a value
     * like any other and is chosen whole, which is what keeps the rules about how many it holds
     * with the one reader that has them — so this is the shape of a list a row is being built
     * <em>into</em>, and not the shape of every list.
     *
     * <p>One element and not however many. What a class at an element asks for is a list holding a
     * value in it; what the other elements are is a separate question, and answering it here would
     * decide it for every rule at once. A list of one holds an element in the class and nothing
     * else, which is the least a row can be and still meet what was asked.
     *
     * @param worn  {@link Node#worn}: every name the position wears, since what is composed here
     *              is bare
     * @param under the element's own position
     * @param least how many the rules say the list holds at the fewest, which is one where they say
     *              nothing. The element being placed is one of them and the rest are values of the
     *              element's type: a class at an element asks for a list holding a value in it, and
     *              a list that met that and broke the rule about how many it holds is not a row
     */
    record Held(TermPath at, Type type, List<TypeOps.Layer> worn, Node under, int least)
            implements Node {

        Held {
            worn = List.copyOf(worn);
            if (least < 1) {
                throw new IllegalArgumentException(
                        "a list built around an element holds it: " + least);
            }
        }
    }

    /**
     * A position composed out of the ones under it.
     *
     * @param of    what the record is called, which is what the composed value is written as
     * @param worn  {@link Node#worn}: every name the position wears, since what is composed here is
     *              bare. Where a requirement narrowed the position, the names it wore before the
     *              narrowing come first and the narrowed value's own after them — one list, because
     *              putting them back on is one thing done once
     * @param under the positions of its fields, in the order the declaration writes them
     */
    record Built(TermPath at, Type type, TypeSymbol of, List<TypeOps.Layer> worn,
                 Map<String, Node> under) implements Node {

        Built {
            worn = List.copyOf(worn);
            under = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(under));
        }
    }

    /**
     * The plan for one parameter.
     *
     * @param decided the paths the caller has already fixed a value at, which are positions this
     *                search does not choose at and does not look under. Not a depth and not a fact
     *                about the type: the caller has what goes there, so what the field of a record
     *                three levels inside it would have offered is nothing this row asks
     */
    static ConstructionPlan of(Type declared, TermPath at, Symbols symbols, Set<TermPath> decided,
                               Requirements required,
                               java.util.function.ToIntBiFunction<TermPath, Type> least) {
        return new ConstructionPlan(node(declared, at, symbols, 0, decided, required, least));
    }

    /** The collections this plan builds out of what stands at their element. */
    List<Held> held() {
        List<Held> out = new ArrayList<>();
        collectHeld(root, out);
        return List.copyOf(out);
    }

    private static void collectHeld(Node node, List<Held> out) {
        switch (node) {
            case Slot _ -> { }
            case Built built -> built.under().values().forEach(each -> collectHeld(each, out));
            case Held held -> {
                out.add(held);
                collectHeld(held.under(), out);
            }
        }
    }

    /** Every position a value is chosen at, in the order they are composed. */
    List<Slot> slots() {
        List<Slot> out = new ArrayList<>();
        collect(root, out);
        return List.copyOf(out);
    }

    private static void collect(Node node, List<Slot> out) {
        switch (node) {
            case Slot slot -> out.add(slot);
            case Built built -> built.under().values().forEach(each -> collect(each, out));
            case Held held -> collect(held.under(), out);
        }
    }

    private static Node node(Type declared, TermPath at, Symbols symbols, int depth,
                             Set<TermPath> decided, Requirements required,
                             java.util.function.ToIntBiFunction<TermPath, Type> least) {
        // Before the narrowing, because a position the caller fixed takes the value it was given
        // whatever a class would have built there.
        if (decided.contains(at)) {
            return new Slot(at, declared, List.of(), true);
        }
        Refinement refinement = required.at(at);
        Type building = refined(declared, refinement, symbols);
        TypeView view = TypeView.of(building, symbols);
        // The position as the narrowing leaves it, which is where every path below it hangs. A
        // refinement is not a step into the value and takes no level of the plan; what it changes is
        // the name of this one position and what may be built at it. Written without it, two cases
        // spreading one record would put two different positions at one name.
        TermPath here = refinement == null ? at : at.refine(refinement);
        // The names the position wore before the narrowing, which are what a value chosen at it is
        // still missing; and those with the narrowed type's own after them, which is what a value
        // composed here bare needs. Both are what the position declares, kept: a value written
        // under the narrowed type's names alone is of a type the parameter does not declare.
        List<TypeOps.Layer> outer =
                refinement == null ? List.of() : TypeView.of(declared, symbols).wrappers();
        List<TypeOps.Layer> worn = refinement == null ? view.wrappers()
                : outside(outer, view.wrappers());
        if (refinement != null && decided.contains(here)) {
            return new Slot(here, building, outer, true);
        }
        // A sequence with something to be placed inside it. Built out of its element rather than
        // chosen whole, since what is being asked for is a list holding a value in a class and no
        // proposal of a whole list can be asked to hold one.
        if (view.shape() instanceof souther.compiler.check.Shape.Sequence sequence
                && depth < MAX_DEPTH) {
            Node inside = node(sequence.element(), here.element(), symbols, depth + 1, decided,
                    required, least);
            if (holdsAFixedPosition(inside)) {
                return new Held(here, building, worn, inside,
                        Math.max(1, least.applyAsInt(here, building)));
            }
        }
        StructuralDescent.Children children = StructuralDescent.of(view.shape());
        // A record with no fields composes nothing out of anything, so it is a value to be chosen
        // like any other and not a position made of positions.
        if (depth >= MAX_DEPTH || children == null || children.under().isEmpty()) {
            return new Slot(here, building, outer, false);
        }
        Map<String, Node> under = new LinkedHashMap<>();
        children.under().forEach((field, type) -> under.put(field,
                node(type, here.then(field), symbols, depth + 1, decided, required, least)));
        return new Built(here, building, children.of(), worn, under);
    }

    /** {@code outer} and then {@code inner}, which is the order names are put back on a value. */
    private static List<TypeOps.Layer> outside(List<TypeOps.Layer> outer,
                                               List<TypeOps.Layer> inner) {
        List<TypeOps.Layer> out = new ArrayList<>(outer);
        out.addAll(inner);
        return List.copyOf(out);
    }

    /**
     * Whether anything under {@code inside} is a position the caller fixed a value at.
     *
     * <p>Asked of the plan that was built for it rather than of how the paths are written. Whether
     * one position is under another is a fact about the steps between them, and a rendering runs
     * those together with whatever each is spelled with — so a test on the text has to name every
     * separator a step can wear, and a position one collection further in follows its container with
     * no dot and matched none of them. Built and then read, the only thing compared is one path with
     * itself.
     */
    private static boolean holdsAFixedPosition(Node inside) {
        // A position the caller narrowed is one it asked something of, as much as one it fixed a
        // value at: a class placing a case inside a list is a class placed under the list. Read off
        // the fixed values alone, a list holding a case of a sum was chosen whole and every element
        // of it came back as whatever stands for the element's type.
        if (inside.at().narrowsWhatItReaches()) {
            return true;
        }
        return switch (inside) {
            case Slot slot -> slot.fixed();
            case Built built -> built.under().values().stream()
                    .anyMatch(ConstructionPlan::holdsAFixedPosition);
            case Held held -> holdsAFixedPosition(held.under());
        };
    }

    /**
     * The type a value is built at: the declared one, unless a refinement narrowed the position.
     *
     * <p>A narrowing of what stands at the position and not a rereading of the declaration. The
     * position's declared type is still the sum, and the axis still says so — a class of it saying
     * which case a witness takes is not the position becoming that case, and reading the two as one
     * would have a later reader believe the model declares something it does not. What moves is what
     * is being built.
     */
    private static Type refined(Type declared, Refinement refinement, Symbols symbols) {
        return switch (refinement) {
            case null -> declared;
            case Refinement.SumCase one -> Type.ref(one.leaf());
            // Nothing builds through one yet. An optional's classes are values a row writes —
            // a value of what it holds, or nothing — and neither is composed field by field, so
            // no requirement of this kind reaches a plan. The day one does, what is built here is
            // what it holds, and that is a decision to make with the row that asks for it rather
            // than one to leave standing as a guess.
            case Refinement.Presence _ -> throw new IllegalStateException(
                    "a value is asked to be built through the presence of an optional at `" + declared
                            + "`; nothing states such a requirement, so this is the generator and"
                            + " the classes disagreeing about what a class asks for");
        };
    }
}
