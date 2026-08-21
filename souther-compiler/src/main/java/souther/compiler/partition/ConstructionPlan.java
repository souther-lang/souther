package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
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
 * spelled with the same {@link TermPath} and are about different things: a class that named a
 * constructor for a sum puts positions under it that the declaration does not have, and a reading of
 * the declaration would not hold them however deep it went. So a path from here is never looked up
 * over there, and the depth this goes to is not the depth a report is about.
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

        /** What is built there — the declared type, unless a recipe named the case to build it
         *  through, or the caller settled the position before this was worked out. */
        Type type();
    }

    /** A position the search chooses a value for. */
    record Slot(TermPath at, Type type) implements Node {}

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
     * @param worn  the newtype names the position is written under, outermost first
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
     * @param of     what the record is called, which is what the composed value is written as
     * @param worn   the newtype names the position is written under, outermost first. A row at a
     *               {@code data SlotN = Slot} carries {@code SlotN(Slot { ... })}, and a value
     *               composed without them is of a type the parameter does not declare
     * @param recipe how a class asked for this to be built, or null where none did
     * @param under  the positions of its fields, in the order the declaration writes them
     */
    record Built(TermPath at, Type type, TypeSymbol of, List<TypeOps.Layer> worn,
                 RepresentativeSource.Evaluation.Compose recipe,
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
    static ConstructionPlan of(Type declared, TermPath at, Symbols symbols, Set<String> decided,
                               Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                               java.util.function.ToIntFunction<TermPath> least) {
        return new ConstructionPlan(node(declared, at, symbols, 0, decided, recipes, least));
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
                             Set<String> decided,
                             Map<String, RepresentativeSource.Evaluation.Compose> recipes,
                             java.util.function.ToIntFunction<TermPath> least) {
        // Before the recipe, because a position the caller fixed takes the value it was given
        // whatever a class would have built there.
        if (decided.contains(at.toString())) {
            return new Slot(at, declared);
        }
        RepresentativeSource.Evaluation.Compose recipe = recipes.get(at.toString());
        Type building = refined(declared, recipe);
        TypeView view = TypeView.of(building, symbols);
        // A sequence with something to be placed inside it. Built out of its element rather than
        // chosen whole, since what is being asked for is a list holding a value in a class and no
        // proposal of a whole list can be asked to hold one.
        if (view.shape() instanceof souther.compiler.check.Shape.Sequence sequence
                && depth < MAX_DEPTH && placesSomethingInside(at, decided)) {
            return new Held(at, building, view.wrappers(),
                    node(sequence.element(), at.element(), symbols, depth + 1, decided, recipes,
                            least),
                    Math.max(1, least.applyAsInt(at)));
        }
        StructuralDescent.Children children = StructuralDescent.of(view.shape());
        // A record with no fields composes nothing out of anything, so it is a value to be chosen
        // like any other and not a position made of positions.
        if (depth >= MAX_DEPTH || children == null || children.under().isEmpty()) {
            return new Slot(at, building);
        }
        Map<String, Node> under = new LinkedHashMap<>();
        children.under().forEach((field, type) -> under.put(field,
                node(type, at.then(field), symbols, depth + 1, decided, recipes, least)));
        return new Built(at, building, children.of(), view.wrappers(), recipe, under);
    }

    /** Whether the caller fixed a value at some position inside the sequence at {@code at}. */
    private static boolean placesSomethingInside(TermPath at, Set<String> decided) {
        String inside = at.element().toString();
        for (String each : decided) {
            if (each.equals(inside) || each.startsWith(inside + ".")) {
                return true;
            }
        }
        return false;
    }

    /**
     * The type a value is built at: the declared one, unless a class named a constructor.
     *
     * <p>A refinement of the position and not a rereading of the declaration. The position's
     * declared type is still the sum, and the axis still says so — a class of it saying which case a
     * witness takes is not the position becoming that case, and reading the two as one would have a
     * later reader believe the model declares something it does not. What moves is what is being
     * built, which is why this is here and not where the input is read.
     */
    private static Type refined(Type declared, RepresentativeSource.Evaluation.Compose recipe) {
        return recipe == null ? declared : Type.ref(recipe.through());
    }
}
