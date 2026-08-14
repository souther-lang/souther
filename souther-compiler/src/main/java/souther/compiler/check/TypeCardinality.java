package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Cardinality;
import souther.compiler.numeric.CardinalityCuts;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * How many values every type has at most, over the declarations a module reaches.
 *
 * <p>An upper bound throughout, and the answer it exists to give is the one at the bottom: a type
 * this puts at none is a type nothing can build. Everything else it says is what makes that answer
 * reachable — a set cannot be filled from an element with fewer values than it holds, and knowing
 * that means counting the element.
 *
 * <p>Rising from none rather than narrowing from anything. A value of a type is built, and a type
 * written in terms of itself with nowhere to stop is one no building ever finishes — so the reading
 * starts by granting nothing and grants a value only where one is shown. Each round bounds the values
 * built in one more step than the last, and where nothing moves, nothing further can be built.
 *
 * <p>Two kinds of place, told apart because only one of them needs the rising. Declarations written
 * in terms of each other are answered together and their answers are rounded to the counts some rule
 * asks about, which is what makes the rising stop. Everywhere else the order of the declarations
 * settles the answers one at a time, and nothing is rounded: a sum of two values is two, and rounding
 * it up to the next count anybody asked about would leave a set drawing on it unable to say it is too
 * small.
 *
 * <p>This says nothing about which declaration is at fault for an answer of none. That is a question
 * about the graph rather than about any one type, and it is asked of these answers rather than while
 * they are found.
 */
public final class TypeCardinality {

    private TypeCardinality() {}

    /** How many values each declaration the module reaches has at most. */
    public static Cardinalities solve(Hir.Module module, Symbols symbols) {
        Map<TypeName, Hir.Def> declared = reached(module, symbols);
        Map<TypeName, Set<TypeName>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        // Fixed before the rising starts. What makes it stop is that there are finitely many answers
        // to rise through, and a count discovered part way would give it somewhere new to go.
        CardinalityCuts cuts = CardinalityCuts.keeping(asked(declared, symbols));
        List<List<TypeName>> components = TypeComponents.of(edges);
        return new Cardinalities(
                Map.copyOf(pass(components, declared, edges, cuts, symbols, Set.of())),
                components, declared, edges, cuts, symbols);
    }

    /**
     * What every declaration came to, and what it would take to ask again.
     *
     * <p>The second is here because one question is asked of these answers afterwards and cannot be
     * asked of the numbers alone: whether a declaration came to none of its own or came to none
     * because something it reads did. Answering it means reading the same declarations again under a
     * different assumption, which is this reading and not another one.
     */
    public static final class Cardinalities {

        private final Map<TypeName, Cardinality> upper;
        private final List<List<TypeName>> components;
        private final Map<TypeName, Hir.Def> declared;
        private final Map<TypeName, Set<TypeName>> edges;
        private final CardinalityCuts cuts;
        private final Symbols symbols;

        private Cardinalities(Map<TypeName, Cardinality> upper, List<List<TypeName>> components,
                              Map<TypeName, Hir.Def> declared,
                              Map<TypeName, Set<TypeName>> edges, CardinalityCuts cuts,
                              Symbols symbols) {
            this.upper = upper;
            this.components = components;
            this.declared = declared;
            this.edges = edges;
            this.cuts = cuts;
            this.symbols = symbols;
        }

        /** How many values every declaration reached has at most. */
        public Map<TypeName, Cardinality> all() {
            return upper;
        }

        /** How many values {@code name} has at most, nothing being known of a name not reached. */
        public Cardinality of(TypeName name) {
            return upper.getOrDefault(name, Cardinality.UNKNOWN);
        }

        /** The declarations with no value, in the order they were reached. */
        Set<TypeName> withNoValue() {
            Set<TypeName> none = new LinkedHashSet<>();
            declared.keySet().forEach(each -> {
                if (of(each).none()) {
                    none.add(each);
                }
            });
            return none;
        }

        /** The declarations that had to be answered together, each before any that reads it. */
        List<List<TypeName>> components() {
            return components;
        }

        /** What each declaration reads. */
        Map<TypeName, Set<TypeName>> edges() {
            return edges;
        }

        /**
         * Every declaration answered again with {@code granted} taken as having values.
         *
         * <p>Read again rather than kept a record of. What a count was is not what it would have
         * been: a record whose only field is an absent value has one value because what the field
         * would hold has none, and one is too few to fill a set of two — so a set with no value can
         * be a set nothing is the matter with, and no reading of which names it reads directly finds
         * that out. Granting the names and taking the answers afresh does.
         */
        Map<TypeName, Cardinality> granting(Set<TypeName> granted) {
            return pass(components, declared, edges, cuts, symbols, granted);
        }
    }

    /**
     * Every declaration answered in an order that has what each reads answered before it, with
     * {@code granted} taken as having values rather than read.
     *
     * <p>Granting is how the question "would this still have no value if that one had one" is asked.
     * The names granted are not read again; everything else is, so a count that was what it was only
     * because of a granted name is answered afresh — a record holding nothing but an absent value has
     * one value, and once the value it lacks is granted it has as many as anything.
     */
    private static Map<TypeName, Cardinality> pass(List<List<TypeName>> components,
                                                   Map<TypeName, Hir.Def> declared,
                                                   Map<TypeName, Set<TypeName>> edges,
                                                   CardinalityCuts cuts, Symbols symbols,
                                                   Set<TypeName> granted) {
        Map<TypeName, Cardinality> solution = new HashMap<>();
        for (List<TypeName> component : components) {
            List<TypeName> asked = new ArrayList<>();
            for (TypeName each : component) {
                if (granted.contains(each)) {
                    solution.put(each, Cardinality.UNKNOWN);
                } else {
                    asked.add(each);
                }
            }
            if (asked.isEmpty()) {
                continue;
            }
            if (asked.size() == 1 && !TypeComponents.recurses(component, edges)) {
                TypeName one = asked.get(0);
                solution.put(one, CardinalityTransfer.upperOf(
                        one, declared.get(one), symbols, solution, granted::contains));
                continue;
            }
            rise(asked, declared, symbols, cuts, solution, granted);
        }
        return solution;
    }

    /**
     * The declarations answered by granting them nothing and granting only what is shown.
     *
     * <p>What they read outside themselves is already answered and is read as it stands. Rounding
     * those too would put the loss of precision at every edge of the graph rather than at the one
     * place the rising needs it.
     */
    private static void rise(List<TypeName> component, Map<TypeName, Hir.Def> declared,
                             Symbols symbols, CardinalityCuts cuts,
                             Map<TypeName, Cardinality> solution, Set<TypeName> granted) {
        for (TypeName each : component) {
            solution.put(each, Cardinality.NO_VALUE);
        }
        boolean moved = true;
        while (moved) {
            moved = false;
            for (TypeName each : component) {
                Cardinality next = cuts.round(CardinalityTransfer.upperOf(
                        each, declared.get(each), symbols, solution, granted::contains));
                if (!next.equals(solution.get(each))) {
                    solution.put(each, next);
                    moved = true;
                }
            }
        }
    }

    /**
     * Every declaration the module's own reach, itself included.
     *
     * <p>A type of another module is one of these. What a declaration comes to is settled by what it
     * is written in terms of wherever that was declared, and stopping at the edge of the module would
     * answer a record by the module its field's type happens to sit in.
     */
    private static Map<TypeName, Hir.Def> reached(Hir.Module module, Symbols symbols) {
        Map<TypeName, Hir.Def> declared = new LinkedHashMap<>();
        List<TypeName> left = new ArrayList<>();
        for (Hir.Def def : module.defs()) {
            left.add(def.declares());
        }
        while (!left.isEmpty()) {
            TypeName name = left.remove(left.size() - 1);
            if (declared.containsKey(name) || !(symbols.declarations().declaration(name) instanceof Hir.Def def)) {
                continue;
            }
            declared.put(name, def);
            left.addAll(read(def, symbols, null));
        }
        return declared;
    }

    /**
     * The declarations {@code def} is written in terms of.
     *
     * <p>Every name written anywhere in its types, at whatever depth. A record naming another record
     * reads that one's answer and no further, but what that one reads it reads in turn, so a name
     * gathered from a depth this one does not itself descend to adds no edge the graph did not have.
     *
     * @param among the names to keep, or null to keep them all
     */
    private static Set<TypeName> read(Hir.Def def, Symbols symbols, Set<TypeName> among) {
        Set<TypeName> named = new LinkedHashSet<>();
        switch (def) {
            case Hir.UnitData _ -> { }
            case Hir.SumData sum -> sum.cases().forEach(each -> named.add(each.denotes()));
            case Hir.Data data ->
                    TypeOps.fieldTypes(data, symbols).values().forEach(each -> names(each, named));
        }
        if (among != null) {
            named.retainAll(among);
        }
        return named;
    }

    private static void names(Type type, Set<TypeName> into) {
        if (type instanceof Type.Ref ref) {
            into.add(ref.name());
            return;
        }
        if (type instanceof Type.Union union) {
            into.addAll(union.members());
            return;
        }
        Type.forEachChild(type, each -> names(each, into));
    }

    /**
     * The counts the rules ask collections to hold, which is what decides the answers worth telling
     * apart.
     *
     * <p>Read off the domain rather than the clauses. A floor arrives in more ways than a number
     * written at the position, and a count missed here is precision lost and nothing else: the
     * answers still tell apart everything the questions found.
     */
    private static Set<Long> asked(Map<TypeName, Hir.Def> declared, Symbols symbols) {
        Set<Long> counts = new HashSet<>();
        declared.forEach((name, def) -> {
            if (!(def instanceof Hir.Data data)) {
                return;
            }
            OccurrenceCounts held = OccurrenceCounts.of(name, data, symbols);
            for (String path : data.newtype() ? Set.of(FieldDomains.THE_VALUE)
                    : TypeOps.fieldTypes(data, symbols).keySet()) {
                long least = held.leastHeldAt(path);
                if (least > 0) {
                    counts.add(least);
                }
            }
        });
        return counts;
    }
}
