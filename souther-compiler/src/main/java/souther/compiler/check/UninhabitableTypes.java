package souther.compiler.check;

import souther.compiler.ast.Hir;
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
 *
 * <p>The search carries no proofs. Which members hold together is a question about the sets, and a
 * proof picked up along the way would be whichever of them the search reached the group by. The
 * proof is taken once the group and the declaration to report it at are both settled, from the one
 * reading that establishes the group: everything outside it granted, and the answer that member came
 * to under that granting.
 */
public final class UninhabitableTypes {

    private UninhabitableTypes() {}

    /**
     * A group of declarations with no value of their own, and what shows it.
     *
     * @param members    every declaration the lack is shared between, wherever they are declared,
     *                   the ones this module writes first and in the order it writes them
     * @param reportedAt the first of them this module declares, which is where the refusal sits
     * @param why        what {@code reportedAt} was shown by, with every lack outside the group
     *                   granted. A proof of the group's own lack and not of the whole module's:
     *                   which member it belongs to is settled before it is taken, so a suggestion
     *                   read off it is about the declaration the refusal points at.
     */
    public record UninhabitableGroup(List<TypeSymbol> members, TypeSymbol reportedAt, Emptiness why) {

        public UninhabitableGroup {
            members = List.copyOf(members);
            if (why == null) {
                throw new IllegalArgumentException(
                        "a declaration reported for having no value was shown to have none: "
                                + reportedAt);
            }
        }
    }

    /**
     * What came of counting a module's declarations, for a reader that is handed the count rather
     * than taking it.
     *
     * <p>Two answers and not a list. A count that came to nothing and a count nobody took are
     * opposite facts about a module — the first says every declaration has a value, the second says
     * nothing at all — and a reader given a list is given the same empty list for both.
     *
     * <p>Why there was no count is not in here. It is said where the count is taken, as what that
     * attempt found, and this says only what a reader of it may conclude. Carried in the value, a
     * reason would be a thing with no equality of its own sitting in an answer everything a module
     * states is compared by.
     */
    public sealed interface WithNoValue {

        /** The groups this module has to report, worked out from what its rules state. */
        record Counted(List<UninhabitableGroup> groups) implements WithNoValue {

            public Counted {
                groups = List.copyOf(groups);
            }
        }

        /** No count was taken, so nothing here says whether any declaration has a value. */
        record NotCounted() implements WithNoValue {}
    }

    /**
     * The groups to report, each at the first of {@code declarations} it holds.
     *
     * <p>Only groups holding one of {@code declarations}: a type of another module having no value
     * is that module's to report, and a type here that has none because of it is left to come right
     * when it does. So what the caller passes is the declarations the report is being made for, and
     * nothing about the rest of the module is read.
     */
    public static List<UninhabitableGroup> withNoValueOfTheirOwn(List<Hir.Def> declarations,
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
        List<UninhabitableGroup> reported = new ArrayList<>();
        for (List<TypeSymbol> group : found) {
            List<TypeSymbol> here = new ArrayList<>(group);
            here.removeIf(each -> !declaredAt.containsKey(each));
            if (here.isEmpty()) {
                continue;
            }
            // The group is one thing to say and is said at the first of them the module declares.
            // Which one that is settles where the report sits and what it is about: the others have
            // no value in the same way, and how each of them reaches the rest is its own.
            here.sort(Comparator.comparingInt(declaredAt::get));
            TypeSymbol at = here.get(0);
            List<TypeSymbol> members = new ArrayList<>(here);
            group.forEach(each -> {
                if (!declaredAt.containsKey(each)) {
                    members.add(each);   // another module's, and named after the ones written here
                }
            });
            reported.add(new UninhabitableGroup(
                    members, at, establishing(group, none, solved).get(at).why()));
        }
        reported.sort(Comparator.comparingInt(each -> declaredAt.get(each.reportedAt())));
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
        Map<TypeSymbol, Cardinality> granted = establishing(these, none, solved);
        List<TypeSymbol> still = new ArrayList<>();
        for (TypeSymbol each : these) {
            if (none.contains(each) && granted.getOrDefault(each, Cardinality.UNKNOWN).none()) {
                still.add(each);
            }
        }
        return still;
    }

    /**
     * Everything answered again with every lack outside {@code these} granted.
     *
     * <p>The reading a group is established by, and so the reading its proofs are taken from. What
     * is granted is settled by the group alone, so asking twice about one group gives one answer and
     * the search reaching it by two paths cannot make it two.
     */
    private static Map<TypeSymbol, Cardinality> establishing(List<TypeSymbol> these,
                                                             Set<TypeSymbol> none,
                                                             TypeCardinality.Cardinalities solved) {
        Set<TypeSymbol> elsewhere = new LinkedHashSet<>(none);
        elsewhere.removeAll(these);
        return solved.granting(elsewhere);
    }
}
