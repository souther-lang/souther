package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicLong;

/**
 * How many values every type has at most, over the declarations a module reaches.
 *
 * <p>An upper bound throughout, and the answer it exists to give is the one at the bottom: a type
 * this puts at none is a type nothing can build. Everything else it says is what makes that answer
 * reachable — a set cannot be filled from an element with fewer values than it holds, and knowing
 * that means counting the element.
 *
 * <p>Rising from nothing shown rather than narrowing from anything. A value of a type is built, and a
 * type written in terms of itself with nowhere to stop is one no building ever finishes — so the
 * reading starts by granting nothing and grants a value only where one is shown. Each round bounds
 * the values built in one more step than the last, and where nothing moves, nothing further can be
 * built.
 *
 * <p>Two kinds of place, told apart because only one of them needs the rising. Declarations written
 * in terms of each other are answered together and their answers are rounded to the counts some rule
 * asks about, which is what makes the rising stop. Everywhere else the order of the declarations
 * settles the answers one at a time, and nothing is rounded: a sum of two values is two, and rounding
 * it up to the next count anybody asked about would leave a set drawing on it unable to say it is too
 * small.
 *
 * <p>The bottom the rising starts from is not an answer and never becomes one. A member the rising
 * has not finished with is at the bottom in {@link Answers}, and a reading resting on one of those is
 * a reading resting on an assumption: writing it down as a proof would have {@code A} shown to have
 * no value because {@code B} has none and {@code B} because {@code A} has, which shows neither.
 * What is true once the rising stops is that the least fixed point was reached with those members
 * still at nothing, so no value of any of them is built in finitely many steps — and that is
 * {@link Emptiness.NoBaseInComponent}, written here and nowhere else.
 *
 * <p>This says nothing about which declaration is at fault for an answer of none. That is a question
 * about the graph rather than about any one type, and it is asked of these answers rather than while
 * they are found.
 */
public final class TypeCardinality {

    private TypeCardinality() {}

    /**
     * Where a count gets what a declaration settles before the rising starts.
     *
     * <p>A capability and not a table: which declarations a count reaches is worked out as it
     * walks, so what is asked for is asked one declaration at a time and nothing has to be gathered
     * before the walk knows where it goes.
     */
    @FunctionalInterface
    public interface Premises {

        /** What {@code named} settles, nothing being settled by a name no declaration answers
         *  for. */
        CardinalityPremise of(TypeSymbol named);

        /** The premises a count reads for itself, for a caller with nowhere to ask. */
        static Premises read(RuleReadingContext reading) {
            return named -> {
                Hir.Def declared =
                        reading.source().symbols().declaredNode(named) instanceof Hir.Def def
                                ? def : null;
                return declared == null ? CardinalityPremise.NOTHING
                        : CardinalityPremise.of(named, declared, reading);
            };
        }
    }

    /**
     * Where a count gets what a declaration outside the ones it is answering came to.
     *
     * <p>Asked as the reading reaches a name rather than gathered before it starts. What a
     * declaration reads is not the names written in its own types alone — a name worn over a value
     * is opened and the reading goes on into what it wraps — so a caller that gathered the counts
     * first would gather everything the declarations reach to hand over the few that are read.
     */
    @FunctionalInterface
    public interface Counts {

        /** What {@code name} came to, nothing being known of a name nobody answers for. */
        Cardinality of(TypeSymbol name);

        /** Nowhere to ask, for a count that holds every declaration it reads. */
        Counts NONE = _ -> null;
    }

    /**
     * Every declaration {@code roots} reaches answered in one walk of the graph.
     *
     * <p>Not the way a compilation counts. A compilation holds an answer per component and is handed
     * what the components a count reads came to ({@link #ofComponent}), so a declaration whose
     * neighbours have not moved is not worked out again; this answers all of them together and is
     * kept for one thing, which is to say what that other way should come to. Two counts of one
     * module differ in what each component was rounded to and in nothing a reader of the report can
     * see, and holding them alike is what says the decomposition changed nothing.
     */
    static Cardinalities overTheWholeGraph(List<? extends TypeSymbol> roots,
                                           RuleReadingContext reading, Premises premises) {
        Symbols symbols = reading.source().symbols();
        Map<TypeSymbol, Hir.Def> declared = reached(roots, symbols);
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        OfTheDeclarations read = ofTheDeclarations(declared.keySet(), premises);
        // Fixed before the rising starts. What makes it stop is that there are finitely many answers
        // to rise through, and a count discovered part way would give it somewhere new to go.
        CardinalityCuts cuts = CardinalityCuts.keeping(read.counts());
        List<List<TypeSymbol>> components = TypeComponents.of(edges);
        return new Cardinalities(
                Map.copyOf(pass(components, declared, edges, cuts, reading, Set.of())),
                components, declared, edges, cuts, reading, read.everyRuleReached());
    }

    /**
     * Which declarations have to be answered together, for everything {@code roots} reach, each of
     * them against the whole of the component it is in.
     *
     * <p>All of them from one walk. Which declarations are one answer is a fact about the graph
     * rather than about any declaration in it, and asking it of one declaration at a time means
     * walking everything that one reaches — so asking it of each of a module's declarations in turn
     * walks the module once per declaration, where the question was the same question every time.
     *
     * <p>In the order two readers of a component would both write it. This says which declarations
     * are one answer, and a set said twice has to be said the same way both times; where they are
     * reported is another question and is asked of what a module declares.
     *
     * <p>Read off the shapes and not off the rules. What reads what is written in the fields and in
     * the names they are written in terms of, so an author changing what a rule allows leaves this
     * where it was.
     */
    public static Map<TypeSymbol, List<TypeSymbol>> componentsOf(List<? extends TypeSymbol> roots,
                                                                 RuleReadingSource source) {
        Symbols symbols = source.symbols();
        Map<TypeSymbol, Hir.Def> declared = reached(roots, symbols);
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        Map<TypeSymbol, List<TypeSymbol>> of = new LinkedHashMap<>();
        for (List<TypeSymbol> component : TypeComponents.of(edges)) {
            List<TypeSymbol> members = component.stream().sorted().toList();
            members.forEach(each -> of.put(each, members));
        }
        return of;
    }

    /**
     * The same for one declaration, worked out from that declaration alone.
     *
     * <p>What a caller with nowhere to ask does. Finding a component means walking everything the
     * declaration reaches, so a caller that did this for each of a module's declarations in turn
     * would walk the module once per declaration; where the components of the module are answered
     * together ({@link #componentsOf}) that walk is made once and this is not wanted.
     */
    public static List<TypeSymbol> componentOf(TypeSymbol named, RuleReadingSource source) {
        Symbols symbols = source.symbols();
        Map<TypeSymbol, Hir.Def> declared = reached(List.of(named), symbols);
        if (!declared.containsKey(named)) {
            return List.of();
        }
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        for (List<TypeSymbol> component : TypeComponents.of(edges)) {
            if (component.contains(named)) {
                return component.stream().sorted().toList();
            }
        }
        return List.of(named);
    }

    /**
     * What the declarations of one component come to, with what they read outside themselves asked
     * of {@code outside}.
     *
     * <p>Asked of somebody rather than worked out here, and that is the whole of what separates this
     * from a count of a module. A component is answered from its own declarations' rules and from
     * what the declarations it reads came to; where those answers come from somebody holding one per
     * component, a component whose neighbours have not moved is not worked out again.
     *
     * <p>The cuts are the component's own and are gathered only where there is a rising to stop.
     * Nothing is rounded where a component is read once, so a component that reads no declaration
     * written in terms of it asks no declaration what counts its rules turn on.
     */
    public static Map<TypeSymbol, Cardinality> ofComponent(List<TypeSymbol> component,
                                                           RuleReadingContext reading,
                                                           Premises premises,
                                                           Counts outside) {
        Symbols symbols = reading.source().symbols();
        Map<TypeSymbol, Hir.Def> declared = new LinkedHashMap<>();
        for (TypeSymbol each : component) {
            if (symbols.declaredNode(each) instanceof Hir.Def def) {
                declared.put(each, def);
            }
        }
        if (declared.isEmpty()) {
            return Map.of();
        }
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        List<TypeSymbol> members = List.copyOf(declared.keySet());
        CardinalityCuts cuts = TypeComponents.recurses(members, edges)
                ? CardinalityCuts.keeping(
                        ofTheDeclarations(reached(members, symbols).keySet(), premises).counts())
                : CardinalityCuts.keeping(Set.of());
        Answers answers = Answers.over(outside);
        settle(members, declared, edges, cuts, reading, Set.of(), answers);
        return answers.everySettled();
    }

    /**
     * The same reading as a count of {@code roots} would be, with what every declaration came to
     * taken from {@code counted} rather than worked out.
     *
     * <p>What is left to do here is everything a count is beside the counts. Which declarations had
     * to be answered together, what each of them reads, and what their rules ask a collection to
     * hold are read off the declarations; they are what the question about which declarations are at
     * fault for a lack is asked of, and none of them is a count.
     */
    public static Cardinalities assembled(List<? extends TypeSymbol> roots,
                                          RuleReadingContext reading,
                                          Premises premises, Counts counted) {
        Symbols symbols = reading.source().symbols();
        Map<TypeSymbol, Hir.Def> declared = reached(roots, symbols);
        Map<TypeSymbol, Set<TypeSymbol>> edges = new LinkedHashMap<>();
        declared.forEach((name, def) -> edges.put(name, read(def, symbols, declared.keySet())));
        OfTheDeclarations read = ofTheDeclarations(declared.keySet(), premises);
        CardinalityCuts cuts = CardinalityCuts.keeping(read.counts());
        Map<TypeSymbol, Cardinality> upper = new LinkedHashMap<>();
        boolean everyCountArrived = true;
        for (TypeSymbol each : declared.keySet()) {
            Cardinality count = counted.of(each);
            everyCountArrived &= count != null;
            upper.put(each, count == null ? Cardinality.UNKNOWN : count);
        }
        return new Cardinalities(Map.copyOf(upper), TypeComponents.of(edges), declared, edges, cuts,
                reading, read.everyRuleReached() && everyCountArrived);
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

        private final Map<TypeSymbol, Cardinality> upper;
        private final List<List<TypeSymbol>> components;
        private final Map<TypeSymbol, Hir.Def> declared;
        private final Map<TypeSymbol, Set<TypeSymbol>> edges;
        private final CardinalityCuts cuts;
        /** The world the readings taken again here are made in, borrowing from the same place the
         *  first pass borrowed from, because it is the same declarations. */
        private final RuleReadingContext reading;
        private final boolean everyRuleReached;

        private Cardinalities(Map<TypeSymbol, Cardinality> upper, List<List<TypeSymbol>> components,
                              Map<TypeSymbol, Hir.Def> declared,
                              Map<TypeSymbol, Set<TypeSymbol>> edges, CardinalityCuts cuts,
                              RuleReadingContext reading, boolean everyRuleReached) {
            this.reading = reading;
            this.everyRuleReached = everyRuleReached;
            this.upper = upper;
            this.components = components;
            this.declared = declared;
            this.edges = edges;
            this.cuts = cuts;
        }

        /** Whether every rule this count read could be read. A count that was short of one says
         *  nothing about a type having no value: the rule it did not get may be the rule that
         *  empties it. */
        public boolean everyRuleReached() {
            return everyRuleReached;
        }

        /** How many values every declaration reached has at most. */
        public Map<TypeSymbol, Cardinality> all() {
            return upper;
        }

        /** How many values {@code name} has at most, nothing being known of a name not reached. */
        public Cardinality of(TypeSymbol name) {
            return upper.getOrDefault(name, Cardinality.UNKNOWN);
        }

        /** The declarations with no value, in the order they were reached. */
        Set<TypeSymbol> withNoValue() {
            Set<TypeSymbol> none = new LinkedHashSet<>();
            declared.keySet().forEach(each -> {
                if (of(each).none()) {
                    none.add(each);
                }
            });
            return none;
        }

        /** The declarations that had to be answered together, each before any that reads it. */
        List<List<TypeSymbol>> components() {
            return components;
        }

        /** What each declaration reads. */
        Map<TypeSymbol, Set<TypeSymbol>> edges() {
            return edges;
        }

        /**
         * What {@code these} and everything they read come to with {@code granted} taken as having
         * values.
         *
         * <p>Read again rather than kept a record of. What a count was is not what it would have
         * been: a record whose only field is an absent value has one value because what the field
         * would hold has none, and one is too few to fill a set of two — so a set with no value can
         * be a set nothing is the matter with, and no reading of which names it reads directly finds
         * that out. Granting the names and taking the answers afresh does. The proofs come back with
         * the counts, so what a declaration is shown by under one supposing is not read off what it
         * was shown by under another.
         *
         * <p>Asked over what {@code these} reach and not over the module. A declaration answers from
         * its own rules and from what it reads, so a name it never reaches has no part in what it
         * comes to however it was supposed — and answering the rest of the module besides would read
         * every declaration of it to say what a few of them come to. The names granted are cut to
         * the same reach for the same reason.
         */
        Map<TypeSymbol, Cardinality> granting(List<? extends TypeSymbol> these,
                                              Set<TypeSymbol> granted) {
            Set<TypeSymbol> reach = reaching(these);
            List<List<TypeSymbol>> within = new ArrayList<>();
            for (List<TypeSymbol> component : components) {
                // A component is reached or it is not: its members read each other, so one of them
                // being reached is all of them being reached.
                if (component.stream().anyMatch(reach::contains)) {
                    within.add(component);
                }
            }
            Set<TypeSymbol> supposed = new LinkedHashSet<>(granted);
            supposed.retainAll(reach);
            // The readings are made afresh — what is asked here is what a declaration would hold if
            // another had values, and no reading with something supposed is a declaration's own —
            // but what has already been made of the declarations is borrowed all the same: what a
            // rule's strings come to is settled by the rule and not by what is supposed beside it.
            return pass(within, declared, edges, cuts, reading, supposed);
        }

        /** {@code these} and every declaration they read, at whatever remove. */
        private Set<TypeSymbol> reaching(List<? extends TypeSymbol> these) {
            Set<TypeSymbol> reach = new LinkedHashSet<>(these);
            List<TypeSymbol> left = new ArrayList<>(reach);
            while (!left.isEmpty()) {
                TypeSymbol name = left.remove(left.size() - 1);
                for (TypeSymbol read : edges.getOrDefault(name, Set.of())) {
                    if (reach.add(read)) {
                        left.add(read);
                    }
                }
            }
            return reach;
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
    private static Map<TypeSymbol, Cardinality> pass(List<List<TypeSymbol>> components,
                                                   Map<TypeSymbol, Hir.Def> declared,
                                                   Map<TypeSymbol, Set<TypeSymbol>> edges,
                                                   CardinalityCuts cuts, RuleReadingContext reading,
                                                   Set<TypeSymbol> granted) {
        Answers answers = Answers.empty();
        for (List<TypeSymbol> component : components) {
            settle(component, declared, edges, cuts, reading, granted, answers);
        }
        return answers.everySettled();
    }

    /**
     * One component answered into {@code answers}, everything it reads outside itself being
     * answered there already.
     *
     * <p>The two kinds of place are told apart here. A declaration that reads nothing written in
     * terms of it is settled from what is already known and nothing is rounded; the rest are
     * answered together by rising, which is what the rounding is for.
     */
    private static void settle(List<TypeSymbol> component, Map<TypeSymbol, Hir.Def> declared,
                               Map<TypeSymbol, Set<TypeSymbol>> edges, CardinalityCuts cuts,
                               RuleReadingContext reading, Set<TypeSymbol> granted,
                               Answers answers) {
        List<TypeSymbol> asked = new ArrayList<>();
        for (TypeSymbol each : component) {
            if (granted.contains(each)) {
                answers.settle(each, Cardinality.UNKNOWN);
            } else {
                asked.add(each);
            }
        }
        if (asked.isEmpty()) {
            return;
        }
        if (asked.size() == 1 && !TypeComponents.recurses(component, edges)) {
            TypeSymbol one = asked.get(0);
            answers.settle(one, transfer(one, declared.get(one), reading, answers, granted));
            return;
        }
        rise(asked, declared, reading, cuts, answers, granted);
    }

    /**
     * The declarations answered by granting them nothing and granting only what is shown.
     *
     * <p>What they read outside themselves is already answered and is read as it stands. Rounding
     * those too would put the loss of precision at every edge of the graph rather than at the one
     * place the rising needs it.
     */
    private static void rise(List<TypeSymbol> component, Map<TypeSymbol, Hir.Def> declared,
                             RuleReadingContext reading, CardinalityCuts cuts,
                             Answers answers, Set<TypeSymbol> granted) {
        component.forEach(answers::atBottom);
        boolean moved = true;
        while (moved) {
            moved = false;
            for (TypeSymbol each : component) {
                Cardinality before = answers.settledAt(each);
                Cardinality next = round(cuts, transfer(
                        each, declared.get(each), reading, answers, granted));
                // Written every round, and the rising is over the counts alone. Two readings that
                // come to none are the same answer to rise through however they were shown, so
                // comparing the proofs would keep a settled rising moving; and taking the earlier
                // proof would leave a declaration carrying what it was shown by before the answers
                // it rests on were what they are.
                answers.settle(each, next);
                if (before == null || !sameCount(before, next)) {
                    moved = true;
                }
            }
        }
        settleUnrounded(component, declared, reading, answers, granted);
        discharge(component, answers);
    }

    /**
     * What the risen declarations come to once nothing is rounded, which is what they answer with.
     *
     * <p>The rounding is what makes the rising stop and is no part of what it found. A count rounded
     * up is a count as far as the questions the cuts were gathered from can tell apart, so an answer
     * carrying one is an answer about those questions as much as about the declaration — and two
     * readers who asked different things of the same declarations would need two of them. Read once
     * more without it and the answer is the declarations' own, whoever holds it.
     *
     * <p>Sound because the rising's answers are upper bounds and a reading over upper bounds is one:
     * what comes out is no wider than what was rounded, since rounding only ever went up. And every
     * member is read from what the rising settled rather than from what this pass has written, so
     * what each comes to is settled by the rising and not by where it sits among the others.
     */
    private static void settleUnrounded(List<TypeSymbol> component,
                                        Map<TypeSymbol, Hir.Def> declared,
                                        RuleReadingContext reading, Answers answers,
                                        Set<TypeSymbol> granted) {
        Map<TypeSymbol, Cardinality> found = new LinkedHashMap<>();
        for (TypeSymbol each : component) {
            found.put(each, transfer(each, declared.get(each), reading, answers, granted));
        }
        found.forEach(answers::settle);
    }

    /** Whether two answers are the same one to rise through, which the proofs have no part in. */
    private static boolean sameCount(Cardinality one, Cardinality other) {
        return one instanceof Cardinality.None
                ? other instanceof Cardinality.None : one.equals(other);
    }

    /**
     * What one declaration comes to under the answers so far, asked from here and counted.
     *
     * <p>Every asking a count makes goes through this, which is what makes the number below mean
     * something. A transfer is what a count spends per declaration per round, and the two places it
     * is asked from — a declaration that settles alone and a declaration in a rising component —
     * are the same spending.
     */
    private static Cardinality transfer(TypeSymbol named, Hir.Def def, RuleReadingContext reading,
                                        Answers answers, Set<TypeSymbol> granted) {
        TRANSFERS.incrementAndGet();
        return CardinalityTransfer.upperOf(named, def, reading, answers, granted);
    }

    /**
     * How many times a count has asked what a declaration comes to, for a test holding a caller to
     * what a count costs.
     *
     * <p>Beside {@link InvariantChecker#readingsMade()} and not in place of it, because the two
     * answer different questions. A reading is made once per declaration per revision and lent to
     * everyone after, so the readings say which declarations an edit reached and say nothing about
     * how often they were worked over. A count that asked the same declaration a hundred times
     * borrows one reading and makes a hundred transfers.
     *
     * <p>Counted rather than timed, for the reason the readings are: what a caller is held to is
     * that a count over a graph twice the size asks twice as much of it, which is a shape and not a
     * speed.
     */
    public static long transfersMade() {
        return TRANSFERS.get();
    }

    private static final AtomicLong TRANSFERS = new AtomicLong();

    private static Cardinality round(CardinalityCuts cuts, Cardinality of) {
        return of instanceof Cardinality.Standing standing ? cuts.round(standing) : of;
    }

    /**
     * The members left with nothing to bottom out, told what showed it once the rising has stopped.
     *
     * <p>A member whose proof rests on another member of the same component was, while the rising
     * ran, resting on an assumption. Which of them were shown something is asked here: a member with
     * a count is one, and so is a member whose proof reaches outside the component or stops at rules
     * of its own — and then any member resting only on those, and so on until nothing more is added.
     * What is left is a set every member of which needs the others, which is a lack no finite
     * building bottoms out of, and the least fixed point having been reached is the proof of it.
     */
    private static void discharge(List<TypeSymbol> component, Answers answers) {
        Set<TypeSymbol> shown = new HashSet<>();
        Set<TypeSymbol> within = Set.copyOf(component);
        boolean added = true;
        while (added) {
            added = false;
            for (TypeSymbol each : component) {
                if (shown.contains(each)) {
                    continue;
                }
                Cardinality count = answers.settledAt(each);
                if (!(count instanceof Cardinality.None it) || restsOn(it.why(), within, shown)) {
                    shown.add(each);
                    added = true;
                }
            }
        }
        if (shown.size() == component.size()) {
            return;
        }
        List<TypeSymbol> without = component.stream().filter(each -> !shown.contains(each)).toList();
        for (TypeSymbol each : without) {
            answers.settle(each, Cardinality.none(new Emptiness.NoBaseInComponent(
                    without, answers.settledAt(each).why())));
        }
    }

    /** Whether every member of {@code within} this proof reaches has been shown something. */
    private static boolean restsOn(Emptiness why, Set<TypeSymbol> within, Set<TypeSymbol> shown) {
        return switch (why) {
            case Emptiness.ConflictingRules _, Emptiness.EmptyNumericInterval _,
                 Emptiness.EmptyOrderedInterval _, Emptiness.NoAllowedValueInRange _,
                 Emptiness.NoAllowedValueWithinRequiredBounds _,
                 Emptiness.NoCommonValueForEqualPositions _,
                 Emptiness.NoDistinctValuesForPositionsHeldApart _,
                 Emptiness.PositionsHeldAsOneAreHeldApart _,
                 Emptiness.SetRequiresTooManyDistinctValues _,
                 Emptiness.NoAllowedCollectionSize _ -> true;
            case Emptiness.TheNameHasNone it ->
                    !within.contains(it.name()) || shown.contains(it.name());
            // Not reachable. A proof read here was built from what a name answers, which is the
            // proof that stops at the name, and this is the only writer of the other one. Answered
            // the way that keeps a member out of the set that was shown something, which is what it
            // would mean if it ever were reached.
            case Emptiness.NoBaseInComponent _ -> false;
            case Emptiness.AtAField it -> restsOn(it.under(), within, shown);
            case Emptiness.AtEqualPositions it -> restsOn(it.under(), within, shown);
            case Emptiness.AtPositionsHeldApart it -> restsOn(it.under(), within, shown);
            case Emptiness.NonEmptyCollectionWithNoElement it ->
                    restsOn(it.element(), within, shown);
            case Emptiness.AcrossEveryCase it ->
                    it.cases().stream().allMatch(each -> restsOn(each, within, shown));
        };
    }

    /**
     * What is declared at {@code roots} and everything those reach, themselves included.
     *
     * <p>A type of another module is one of these. What a declaration comes to is settled by what it
     * is written in terms of wherever that was declared, and stopping at the edge of the module would
     * answer a record by the module its field's type happens to sit in.
     */
    private static Map<TypeSymbol, Hir.Def> reached(List<? extends TypeSymbol> roots,
                                                    Symbols symbols) {
        Map<TypeSymbol, Hir.Def> declared = new LinkedHashMap<>();
        List<TypeSymbol> left = new ArrayList<>(roots);
        while (!left.isEmpty()) {
            TypeSymbol name = left.remove(left.size() - 1);
            if (declared.containsKey(name) || !(symbols.declaredNode(name) instanceof Hir.Def def)) {
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
    private static Set<TypeSymbol> read(Hir.Def def, Symbols symbols, Set<TypeSymbol> among) {
        Set<TypeSymbol> named = new LinkedHashSet<>();
        switch (def) {
            case Hir.UnitData _ -> { }
            // A case naming nothing names no declaration for this to have read.
 	    case Hir.SumData sum -> sum.cases().forEach(each -> {
                if (each instanceof Hir.Name.Denoting names) {
                    named.add(names.type());
                }
            });
            case Hir.Data data ->
                    TypeOps.fieldTypes(data, symbols).values().forEach(each -> names(each, named));
        }
        if (among != null) {
            named.retainAll(among);
        }
        return named;
    }

    private static void names(Type type, Set<TypeSymbol> into) {
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
     * What reading every declaration the count reaches says about the count.
     *
     * @param counts           the counts the rules ask collections to hold, which is what decides
     *                         the answers worth telling apart
     * @param everyRuleReached whether every rule those readings were to be built on arrived
     */
    private record OfTheDeclarations(Set<Long> counts, boolean everyRuleReached) {}

    /**
     * Both of those, gathered from what each declaration the count reaches settles on its own.
     *
     * <p>A union and an and, which is the whole of what this does with them: what a declaration
     * asks about is asked wherever it is reached from, and a count short of one rule is short
     * however many others arrived. So nothing here is a fact about the set of declarations, and
     * every declaration that is not reached contributes nothing rather than something empty.
     */
    private static OfTheDeclarations ofTheDeclarations(Set<TypeSymbol> declared,
                                                      Premises premises) {
        Set<Long> counts = new HashSet<>();
        boolean everyRuleReached = true;
        for (TypeSymbol each : declared) {
            CardinalityPremise premise = premises.of(each);
            counts.addAll(premise.counts());
            everyRuleReached &= premise.everyRuleReached();
        }
        return new OfTheDeclarations(counts, everyRuleReached);
    }
}
