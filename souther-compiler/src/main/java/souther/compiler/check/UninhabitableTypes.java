package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.numeric.Cardinality;
import souther.compiler.types.TypeName;

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
 * <p>The question is asked of the declarations that are answered together, and the answer is about
 * the members. Two written in terms of each other are one thing to say only where both are left with
 * none; where one of them has a rule of its own that leaves it nothing, it is named and the other,
 * which was answering for it, is not.
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
        Set<TypeName> ofTheirOwn = new LinkedHashSet<>();
        for (List<TypeName> together : solved.components()) {
            if (together.stream().noneMatch(none::contains)) {
                continue;
            }
            Set<TypeName> elsewhere = new LinkedHashSet<>(none);
            elsewhere.removeAll(together);
            Map<TypeName, Cardinality> granted = solved.granting(elsewhere);
            for (TypeName each : together) {
                if (none.contains(each)
                        && granted.getOrDefault(each, Cardinality.UNKNOWN).none()) {
                    ofTheirOwn.add(each);
                }
            }
        }
        List<List<TypeName>> reported = new ArrayList<>();
        for (List<TypeName> group : TypeComponents.of(amongThemselves(ofTheirOwn, solved))) {
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
     * Which of these each of them reads.
     *
     * <p>Grouped again among themselves rather than taken as the groups they were answered in. Two
     * answered together are one thing to say only while both are left with none, and the one that
     * was answering for the other is out by the time this is asked.
     */
    private static Map<TypeName, Set<TypeName>> amongThemselves(
            Set<TypeName> ofTheirOwn, TypeCardinality.Cardinalities solved) {
        Map<TypeName, Set<TypeName>> among = new LinkedHashMap<>();
        ofTheirOwn.forEach(each -> among.put(each, new LinkedHashSet<>()));
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
