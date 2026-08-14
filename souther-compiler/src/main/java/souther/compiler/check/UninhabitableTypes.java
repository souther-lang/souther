package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Cardinality;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which declarations to say have no value, out of all the ones that have none.
 *
 * <p>Having none spreads. A record holding a type nothing can build cannot be built either, and so
 * can everything holding that, so the declarations with no value are rarely the declaration anything
 * is the matter with. Said of all of them, the one thing the author has to change is somewhere in a
 * list of things that will come right when it does.
 *
 * <p>What separates them is granting. A set of declarations <em>holds</em> when taking every other
 * lack to be a value and reading them all again leaves every one of that set with none: nothing
 * outside accounts for what they lack, so whatever accounts for it is among them. What is reported is
 * the smallest sets that hold. A set with a smaller one inside it that holds was two questions asked
 * as one, and the smaller is the answer; a set with none inside it is a lack every member of which
 * needs the others, and there is no first among them to name.
 *
 * <p>Read again rather than followed along edges. What a count was is not what it would have been:
 * a record whose only field is an absent value has one value because what the field would hold has
 * none, and one is too few to fill a set of two — so a set with no value can be one nothing is the
 * matter with, with no declaration between them having no value for an edge to run through.
 *
 * <p>Being answered together is where the search starts and not what it answers. Declarations are
 * read in one rising because they are written in terms of each other, which is about the recursion:
 * two recursions that may each hold the other's values are one reading and two lacks, and a
 * declaration that merely reads one is neither. A set that holds does lie inside one such reading —
 * a set spanning two of them has a part in the one the other does not read, and granting that part
 * leaves the rest where it was — so that is as far as the search has to look.
 *
 * <p>Taking one away at a time finds every smallest one. Where a set that holds has a smaller one
 * inside it, every member outside the smaller one can be taken away with the smaller one left whole,
 * so some single removal leaves something holding; and where no single removal does, there is
 * nothing smaller to find.
 */
public final class UninhabitableTypes {

    private UninhabitableTypes() {}

    /**
     * The groups of declarations to report, each in the order {@code declarations} are written in.
     *
     * <p>Only groups holding one of {@code declarations}: a type of another module having no value
     * is that module's to report, and a type here that has none because of it is left to come right
     * when it does. So what the caller passes is the declarations the report is being made for, and
     * nothing about the rest of the module is read.
     */
    public static List<List<TypeSymbol>> withNoValueOfTheirOwn(List<Hir.Def> declarations,
                                                             TypeCardinality.Cardinalities solved) {
        Map<TypeSymbol, Integer> declaredAt = new LinkedHashMap<>();
        for (Hir.Def def : declarations) {
            declaredAt.put(def.declares(), declaredAt.size());
        }
        Set<TypeSymbol> none = solved.withNoValue();
        if (none.isEmpty()) {
            return List.of();   // nothing to tell apart, and nothing to read again to do it
        }
        Set<List<TypeSymbol>> found = new LinkedHashSet<>();
        for (List<TypeSymbol> together : solved.components()) {
            // Reading them all again is what answers this, so it is asked only where there is
            // something to ask about: a module whose declarations all have values would otherwise be
            // read once more for every group of them.
            if (together.stream().anyMatch(none::contains)) {
                smallestThatHold(together, none, solved, found);
            }
        }
        List<List<TypeSymbol>> reported = new ArrayList<>();
        for (List<TypeSymbol> group : found) {
            List<TypeSymbol> here = new ArrayList<>(group);
            here.removeIf(each -> !declaredAt.containsKey(each));
            if (here.isEmpty()) {
                continue;
            }
            here.sort(Comparator.comparingInt(declaredAt::get));
            reported.add(List.copyOf(here));
        }
        reported.sort(Comparator.comparingInt(each -> declaredAt.get(each.get(0))));
        return List.copyOf(reported);
    }

    /**
     * The smallest sets inside {@code these} that hold, collected into {@code found}.
     *
     * <p>What is left of a set once everything else is granted is the largest part of it that holds,
     * and where nothing is left, every one of them was answering for something else. Where something
     * is left, each of its members is taken away in turn and the question asked of what remains: a
     * removal that leaves something holding says the set was not the smallest, and where no removal
     * does, it is.
     */
    private static void smallestThatHold(List<TypeSymbol> these, Set<TypeSymbol> none,
                                         TypeCardinality.Cardinalities solved,
                                         Set<List<TypeSymbol>> found) {
        List<TypeSymbol> holds = whatHoldsIn(these, none, solved);
        if (holds.isEmpty()) {
            return;
        }
        Set<List<TypeSymbol>> smaller = new LinkedHashSet<>();
        for (TypeSymbol one : holds) {
            List<TypeSymbol> rest = new ArrayList<>(holds);
            rest.remove(one);
            List<TypeSymbol> inside = whatHoldsIn(rest, none, solved);
            if (!inside.isEmpty()) {
                smaller.add(inside);
            }
        }
        if (smaller.isEmpty()) {
            found.add(List.copyOf(holds));
            return;
        }
        for (List<TypeSymbol> each : smaller) {
            smallestThatHold(each, none, solved, found);
        }
    }

    /**
     * The largest part of {@code these} that holds.
     *
     * <p>What falls out is granted to what is left, so the question is asked again until nothing more
     * falls out. What remains is a set every member of which has no value with everything outside it
     * granted, which is the whole of what holding is.
     */
    private static List<TypeSymbol> whatHoldsIn(List<TypeSymbol> these, Set<TypeSymbol> none,
                                              TypeCardinality.Cardinalities solved) {
        List<TypeSymbol> now = these;
        while (true) {
            List<TypeSymbol> next = leftWithNone(now, none, solved);
            if (next.size() == now.size()) {
                return next;
            }
            now = next;
        }
    }

    /** Which of {@code these} still have no value once every lack outside them is granted. */
    private static List<TypeSymbol> leftWithNone(List<TypeSymbol> these, Set<TypeSymbol> none,
                                               TypeCardinality.Cardinalities solved) {
        Set<TypeSymbol> elsewhere = new LinkedHashSet<>(none);
        elsewhere.removeAll(these);
        Map<TypeSymbol, Cardinality> granted = solved.granting(elsewhere);
        List<TypeSymbol> still = new ArrayList<>();
        for (TypeSymbol each : these) {
            if (none.contains(each) && granted.getOrDefault(each, Cardinality.UNKNOWN).none()) {
                still.add(each);
            }
        }
        return still;
    }
}
