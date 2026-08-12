package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Cardinality;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.Collection;
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
 * <p>What separates them is asked by granting: take every other declaration that has no value to have
 * one, read them all again, and see which are left with none. A declaration that has none whatever
 * else is granted has none of its own; one that stops is a declaration that was answering for
 * something else.
 *
 * <p>Read again rather than followed along edges. What a count was is not what it would have been:
 * a record whose only field is an absent value has one value because what the field would hold has
 * none, and one is too few to fill a set of two — so a set with no value can be one nothing is the
 * matter with, with no declaration between them having no value for an edge to run through. Only
 * granting and reading afresh finds that.
 *
 * <p>And asked again of whatever it separates. Granting is asked of a set of declarations, so the
 * answer is only ever about that set: two told apart by one round are two sets nobody has yet asked
 * about, and one of them may be answering for the other. Each round either leaves its set whole — in
 * which case there is nothing further to tell apart and the set is what is said — or breaks it, and
 * every piece is asked the same question. The pieces are smaller each time, so this ends.
 */
public final class UninhabitableTypes {

    private UninhabitableTypes() {}

    /**
     * The groups of declarations to report, each in the order the module declares them.
     *
     * <p>Only groups holding a declaration of {@code module}: a type of another module having no
     * value is that module's to report, and a type here that has none because of it is left to come
     * right when it does.
     */
    public static List<List<TypeName>> withNoValueOfTheirOwn(Ast.Module module, Symbols symbols,
                                                             TypeCardinality.Cardinalities solved) {
        Map<TypeName, Integer> declaredAt = new LinkedHashMap<>();
        for (Ast.Def def : module.defs()) {
            declaredAt.put(symbols.own(def.name()), declaredAt.size());
        }
        Set<TypeName> none = solved.withNoValue();
        List<List<TypeName>> found = new ArrayList<>();
        for (List<TypeName> together : solved.components()) {
            tellApart(together, none, solved, found);
        }
        List<List<TypeName>> reported = new ArrayList<>();
        for (List<TypeName> group : found) {
            List<TypeName> here = new ArrayList<>(group);
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
     * What is left of {@code group} once every lack outside it is granted, told apart as far as it
     * goes.
     *
     * <p>Whole and in one piece is the answer: nothing in it is answering for anything else that
     * still has none, so it is one thing to say. Anything else is a set nobody asked about — the ones
     * that dropped out were part of what the rest were asked beside — so each piece is asked again on
     * its own, and what falls out of one round is granted in the next.
     */
    private static void tellApart(List<TypeName> group, Set<TypeName> none,
                                  TypeCardinality.Cardinalities solved, List<List<TypeName>> found) {
        Set<TypeName> elsewhere = new LinkedHashSet<>(none);
        elsewhere.removeAll(group);
        Map<TypeName, Cardinality> granted = solved.granting(elsewhere);
        List<TypeName> still = new ArrayList<>();
        for (TypeName each : group) {
            if (none.contains(each) && granted.getOrDefault(each, Cardinality.UNKNOWN).none()) {
                still.add(each);
            }
        }
        if (still.isEmpty()) {
            return;   // every one of them was answering for something else
        }
        List<List<TypeName>> pieces = TypeComponents.of(amongThemselves(still, solved));
        if (still.size() == group.size() && pieces.size() == 1) {
            found.add(pieces.get(0));
            return;
        }
        for (List<TypeName> piece : pieces) {
            tellApart(piece, none, solved, found);
        }
    }

    /**
     * Which of these each of them reads.
     *
     * <p>Grouped among themselves rather than taken as the group they were answered in. Two answered
     * together are one thing to say only while both are left with none, and the one that was
     * answering for the other is out by the time this is asked.
     */
    private static Map<TypeName, Set<TypeName>> amongThemselves(
            Collection<TypeName> these, TypeCardinality.Cardinalities solved) {
        Map<TypeName, Set<TypeName>> among = new LinkedHashMap<>();
        these.forEach(each -> among.put(each, new LinkedHashSet<>()));
        among.forEach((name, reads) -> {
            for (TypeName each : solved.edges().getOrDefault(name, Set.of())) {
                if (among.containsKey(each)) {
                    reads.add(each);
                }
            }
        });
        return among;
    }
}
