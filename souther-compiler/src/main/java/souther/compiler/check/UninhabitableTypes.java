package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
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
 * <p>Two readings narrow it. Declarations written in terms of each other have no value together and
 * are one thing to say — there is no first among them, and naming each in turn says the same thing
 * three times. And a group that stops having none once what it reads is granted anything was never
 * the matter: it is the group it reads that is, and that one is named instead.
 *
 * <p>What is left is a group whose having no value survives everything around it being granted a
 * value. Where the count came from does not enter into it: a recursion with nowhere to stop, rules
 * that cannot all hold, and a collection asking for more than it can be given are all groups of this
 * kind and are told apart by nothing here.
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
        Map<TypeName, Set<TypeName>> among = amongThoseWithNoValue(solved);
        List<List<TypeName>> reported = new ArrayList<>();
        for (List<TypeName> component : TypeComponents.of(among)) {
            List<TypeName> here = new ArrayList<>(component);
            here.removeIf(each -> !declaredAt.containsKey(each));
            if (here.isEmpty() || !solved.noValueOfItsOwn(component)) {
                continue;
            }
            here.sort(java.util.Comparator.comparingInt(declaredAt::get));
            reported.add(List.copyOf(here));
        }
        reported.sort(java.util.Comparator.comparingInt(each -> declaredAt.get(each.get(0))));
        return List.copyOf(reported);
    }

    /**
     * The declarations with no value, and which of them each reads.
     *
     * <p>Kept to those with no value, so that what comes out of the walk is the groups of them: an
     * edge to a declaration that has a value is an edge to somewhere this question does not go.
     */
    private static Map<TypeName, Set<TypeName>> amongThoseWithNoValue(
            TypeCardinality.Cardinalities solved) {
        Map<TypeName, Set<TypeName>> among = new LinkedHashMap<>();
        solved.all().forEach((name, count) -> {
            if (count.none()) {
                among.put(name, new LinkedHashSet<>());
            }
        });
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
