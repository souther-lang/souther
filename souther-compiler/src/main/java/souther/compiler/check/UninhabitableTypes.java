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
 * <p>Asked of one declaration first. A declaration that has no value with every other lack granted
 * has one nobody else can account for, and it is said on its own — whatever else it happens to be
 * read together with. Being read together is about a recursion and says nothing about whose lack it
 * is: two written in terms of each other have nothing outside them to grant, and one of them can
 * still be the only one with a rule of its own.
 *
 * <p>What is left over lacks in company. Two that have no value only through each other are one
 * thing to say, since neither is what the author changes, and they are said as the declarations they
 * are read together with — less whichever of them was already said on its own. A group of those is
 * reported where granting every lack outside it leaves all of them with none, and dropped where it
 * does not, which is what takes out a record holding a recursion that has nowhere to stop.
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
        if (none.isEmpty()) {
            return List.of();   // nothing to tell apart, and nothing to read again to do it
        }
        List<List<TypeName>> found = new ArrayList<>();
        Set<TypeName> alone = new LinkedHashSet<>();
        for (TypeName each : none) {
            if (leftWithNone(List.of(each), none, solved).size() == 1) {
                alone.add(each);
                found.add(List.of(each));
            }
        }
        for (List<TypeName> together : solved.components()) {
            List<TypeName> sharing = new ArrayList<>(together);
            sharing.removeIf(each -> !none.contains(each) || alone.contains(each));
            if (!sharing.isEmpty()
                    && leftWithNone(sharing, none, solved).size() == sharing.size()) {
                found.add(List.copyOf(sharing));
            }
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
     * Which of {@code these} still have no value once every lack outside them is granted.
     *
     * <p>All of them is the answer that names them: nothing outside accounts for it, so whatever
     * accounts for it is here. Fewer than all is a set that was two questions asked as one, and the
     * ones that dropped out were answering for the ones that did not.
     */
    private static List<TypeName> leftWithNone(List<TypeName> these, Set<TypeName> none,
                                               TypeCardinality.Cardinalities solved) {
        Set<TypeName> elsewhere = new LinkedHashSet<>(none);
        elsewhere.removeAll(these);
        Map<TypeName, Cardinality> granted = solved.granting(elsewhere);
        List<TypeName> still = new ArrayList<>();
        for (TypeName each : these) {
            if (none.contains(each) && granted.getOrDefault(each, Cardinality.UNKNOWN).none()) {
                still.add(each);
            }
        }
        return still;
    }

}
