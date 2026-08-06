package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation).
 *
 * <p>These are the tables that decide how much of a model the language tracks rather than leaves to a
 * run-time check, and each is stated per operation because that is the level an author writes at. It
 * is data and lookups and nothing else: what a rule is <em>used for</em> — carrying a predicate to
 * the container something was built from, naming a size — is the walk's, and lives with the walk.
 *
 * <p>Every rule is keyed by the operation a call reaches, not by how it was written: a module that
 * imported an operation writes it bare and one that did not writes it qualified, and they are the
 * same operation. What the operations do to the closure they are handed is not here but in
 * {@link Combinators}, which the totality check reads as well and neither of the two states.
 *
 * <p>A rule answers a call, not a position in one. Which argument it reads is written as {@link Reads}
 * and settled here, so no reader turns a number back into an argument and none has to ask whether the
 * number was one this call has. What makes that safe is the binding below: every row is held to the
 * declaration it was written for before any of them is read.
 */
final class DischargeRules {

    /** The library operation written {@code qualified}, as what a name reaching it denotes. */
    private static ValueName op(String qualified) {
        return new ValueName.Stdlib(qualified);
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two. */
    private static final Set<ValueName> SIZE_CALLS = Set.of(
            op("List.length"), op("String.length"), op("Set.size"), op("Map.size"));

    /**
     * What a construction of a container keeps of the container it was built from.
     *
     * <ul>
     * <li>{@code PERMUTES} — the same elements in another order. Everything survives.
     * <li>{@code SUBSET} — some of the same elements. Nothing new is there, so a property of every
     *     element survives and the size can only fall.
     * <li>{@code MAPS} — one new element for each. As many as before, and nothing is known of what
     *     they are.
     * <li>{@code COLLAPSES} — at most one new element for each. Neither the elements nor the count.
     * </ul>
     */
    enum Shape {
        PERMUTES, SUBSET, MAPS, COLLAPSES;

        /** Whether the result has exactly as many as the container it was built from. */
        boolean keepsSize() {
            return this == PERMUTES || this == MAPS;
        }
    }

    /**
     * Which argument a rule reads.
     *
     * <p>Either the position the declaration puts it at, or the part it plays in what the operation
     * hands its closure — which {@link Combinators} already reads off the signature. A rule that names
     * the part restates nothing and cannot come to disagree with the declaration; one that writes a
     * position is a decision the signature does not settle, and is held to the declaration where the
     * tables are bound.
     *
     * <p>Nothing outside this asks for the number. A reader is answered with the argument.
     */
    sealed interface Reads {

        /** Which parameter of {@code operation} this names. */
        int positionIn(ValueName operation);

        /** The argument {@code call} passes there. */
        default Core of(Core.PreservedCall call) {
            return call.args().get(positionIn(call.operation()));
        }

        /** {@code call} with that argument replaced by {@code value}. */
        default Core.PreservedCall replacedIn(Core.PreservedCall call, Core value) {
            List<Core> args = new ArrayList<>(call.args());
            args.set(positionIn(call.operation()), value);
            return new Core.PreservedCall(call.operation(), args, call.type(), call.pos());
        }

        /** The argument at a written position. */
        record At(int position) implements Reads {
            @Override
            public int positionIn(ValueName operation) {
                return position;
            }
        }

        /** The argument holding what the operation hands its closure. */
        record TheContainer() implements Reads {
            @Override
            public int positionIn(ValueName operation) {
                return handing(operation, "the container").containerArg();
            }
        }

        /** The argument the operation applies to what a container holds. */
        record TheClosure() implements Reads {
            @Override
            public int positionIn(ValueName operation) {
                return handing(operation, "the closure").closureArg();
            }
        }

        private static Combinators.Combinator handing(ValueName operation, String part) {
            Combinators.Combinator handed = Combinators.of(operation);
            if (handed == null) {
                throw new IllegalStateException("a rule about " + operation.name() + " names " + part
                        + " of what it hands its closure, and its signature says it hands one nothing"
                        + " a container holds");
            }
            return handed;
        }
    }

    /** The argument the signature already says the elements come from, where the operation takes a
     * closure at all — so a rule about such an operation writes no position of its own. */
    private static final Reads CONTAINER = new Reads.TheContainer();

    /** The closure itself, for a rule stated over what the closure answers. */
    private static final Reads CLOSURE = new Reads.TheClosure();

    /** The argument at {@code position}, for an operation whose signature does not say which one it
     * is: one that takes no closure, or one given two containers. */
    private static Reads at(int position) {
        return new Reads.At(position);
    }

    /** Which argument a container was built from, and what the building keeps of it. */
    record Built(Reads from, Shape shape) {}

    /** The container {@code call} built its result from, and what the building kept of it. */
    record Source(Core container, Shape shape) {}

    private static final Map<ValueName, Built> BUILT_FROM = Map.ofEntries(
            Map.entry(op("List.reverse"), new Built(at(0), Shape.PERMUTES)),
            Map.entry(op("List.sort"), new Built(at(0), Shape.PERMUTES)),
            Map.entry(op("List.sortBy"), new Built(CONTAINER, Shape.PERMUTES)),
            Map.entry(op("List.map"), new Built(CONTAINER, Shape.MAPS)),
            Map.entry(op("List.mapIndexed"), new Built(CONTAINER, Shape.MAPS)),
            Map.entry(op("Map.mapValues"), new Built(CONTAINER, Shape.MAPS)),
            Map.entry(op("List.filter"), new Built(CONTAINER, Shape.SUBSET)),
            Map.entry(op("List.distinct"), new Built(at(0), Shape.SUBSET)),
            Map.entry(op("List.take"), new Built(at(1), Shape.SUBSET)),
            Map.entry(op("List.drop"), new Built(at(1), Shape.SUBSET)),
            Map.entry(op("Set.filter"), new Built(CONTAINER, Shape.SUBSET)),
            Map.entry(op("Map.filterEntries"), new Built(CONTAINER, Shape.SUBSET)),
            Map.entry(op("List.distinctBy"), new Built(CONTAINER, Shape.SUBSET)),
            Map.entry(op("Map.remove"), new Built(at(1), Shape.SUBSET)),
            Map.entry(op("Set.remove"), new Built(at(1), Shape.SUBSET)),
            Map.entry(op("Map.intersection"), new Built(at(0), Shape.SUBSET)),
            Map.entry(op("Map.difference"), new Built(at(0), Shape.SUBSET)),
            Map.entry(op("Set.intersection"), new Built(at(0), Shape.SUBSET)),
            Map.entry(op("Set.difference"), new Built(at(0), Shape.SUBSET)),
            Map.entry(op("Map.updateIfPresent"), new Built(CONTAINER, Shape.MAPS)),
            Map.entry(op("List.filterMap"), new Built(CONTAINER, Shape.COLLAPSES)),
            Map.entry(op("Set.map"), new Built(CONTAINER, Shape.COLLAPSES)));

    /**
     * The constructions this says nothing of, in three groups. Each reason is about what a shape can
     * say, not about the operation being uninteresting.
     *
     * <p>What they answer holds something other than what they read. A map's keys and its entry
     * pairs are not its values, {@code fromList} takes the values out of pairs, {@code groupBy}
     * answers lists of the elements rather than the elements, {@code concat} reads the lists inside
     * its argument, {@code zipShortest} pairs two lists, and {@code flatMap} makes any number of
     * elements from each — which is neither the elements nor a count.
     *
     * <p>They put in what the container they read did not hold. Nothing that held of every element
     * still does, and the size can rise; a shape says neither of those.
     *
     * <p>They answer the same elements in a container of another kind. That is true and unsayable:
     * every statement the check makes names the kind it is about — {@code List.length} and
     * {@code List.all}, or {@code Set.size} and {@code Set.contains} — so nothing said of the one is
     * a statement about the other, and a rule between them would carry nothing. A statement that
     * spans kinds is what would have to exist first.
     */
    static final Set<ValueName> NOTHING_KEPT = Set.of(
            op("Map.keys"), op("Map.toList"), op("Map.fromList"), op("List.groupBy"),
            op("List.concat"), op("List.zipShortest"), op("List.flatMap"),
            op("Map.insert"), op("Set.insert"), op("Map.union"), op("Set.union"),
            op("List.append"), op("Map.updateOrInsert"),
            op("Map.values"), op("Set.toList"), op("Set.fromList"), op("List.indexBy"));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.contains} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    record Carried(Reads container, Set<Shape> through) {}

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List.all"), new Carried(CONTAINER, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.allDistinctBy"), new Carried(CONTAINER, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List.any"), new Carried(CONTAINER, Set.of(Shape.PERMUTES)),
            op("List.contains"), new Carried(at(1), Set.of(Shape.PERMUTES)),
            op("Set.contains"), new Carried(at(1), Set.of(Shape.PERMUTES)),
            op("Map.containsKey"), new Carried(at(1), Set.of(Shape.PERMUTES)));

    /** Where a predicate reads its container at a call, and how far its statement travels. */
    record Carrying(Core.PreservedCall stated, Reads at, Set<Shape> through) {

        Core container() {
            return at.of(stated);
        }

        /** {@code call} — a call to the same operation — with the container it reads replaced. */
        Core.PreservedCall over(Core.PreservedCall call, Core container) {
            if (!call.operation().equals(stated.operation())) {
                throw new IllegalStateException("a rule read for " + stated.operation().name()
                        + " was asked to rewrite a call to " + call.operation().name());
            }
            return at.replacedIn(call, container);
        }
    }

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, Reads> PROJECTION_OF =
            Map.of(op("List.allDistinctBy"), CLOSURE);

    /** The projection a predicate at a call is stated over, as the block it answers with. */
    record Projection(Core.PreservedCall stated, Reads at, Core.Block projection) {

        /** The call this was read for, stated over {@code value} instead. */
        Core.PreservedCall over(Core value) {
            return at.replacedIn(stated, value);
        }
    }

    /** The calls that state their predicate of <em>every</em> element, so what they say of a
     * container is what holds of each element a closure is handed. Which argument is the predicate
     * and which the container is what {@link Combinators} already answers of any combinator, and how
     * far the statement travels is what {@link #carried} already answers of any predicate — so a
     * quantifier is the name and nothing else. {@code List.all} is the only one the library has. */
    private static final Set<ValueName> QUANTIFIERS = Set.of(op("List.all"));

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property but about what a predicate <em>says</em>: {@code List.isEmpty(xs)} and
     * {@code List.length(xs) == 0} are one statement, so a guard writing either discharges a clause
     * writing the other. Without it the two would be unrelated, which is an accident of which one the
     * author reached for. */
    private static final Map<ValueName, ValueName> EMPTINESS = Map.of(
            op("List.isEmpty"), op("List.length"),
            op("Set.isEmpty"), op("Set.size"),
            op("Map.isEmpty"), op("Map.size"),
            op("String.isEmpty"), op("String.length"));

    /** The predicates whose statement this carries nowhere. A predicate over a string states
     * something of the characters it holds in the order it holds them, and what would carry such a
     * statement is a construction of a container from a container — which a string is not one of,
     * its length being all this names of it. An emptiness check states a size, which travels as a
     * size does ({@link #EMPTINESS}) and not as a property of elements. */
    static final Set<ValueName> NOTHING_CARRIED = Set.of(
            op("String.contains"), op("String.startsWith"), op("String.endsWith"),
            op("String.matches"),
            op("List.isEmpty"), op("Set.isEmpty"), op("Map.isEmpty"), op("String.isEmpty"));

    /** The predicates of a single container that are not emptiness checks. The library has none:
     * every one-argument predicate it declares over a container or a string is one, and one that was
     * not would be named here with what it says instead. */
    static final Set<ValueName> NOT_AN_EMPTINESS_CHECK = Set.of();

    /** The predicates that apply a predicate to what a container holds without stating it of every
     * element. {@code List.any} states it of some, so what it says of the container says nothing
     * about the element a closure is handed. */
    static final Set<ValueName> NOT_A_QUANTIFIER = Set.of(op("List.any"));

    /** The predicates that compute something other than a truth value from each element and are not
     * stated over it. The library has none: {@code allDistinctBy} is the only such predicate and its
     * projection is its closure's answer. */
    static final Set<ValueName> NOT_STATED_OVER_A_PROJECTION = Set.of();

    /** The numbers answered about a container that are not one of its sizes. The library has none:
     * every {@code Int} it answers about a container is how many it holds. */
    static final Set<ValueName> NOT_A_SIZE = Set.of();

    /**
     * The library's function forms of the arithmetic operators, and the operator each one is. They
     * reach the same kernel in the same argument order — {@code Int.add} is {@code IntMath.addExact},
     * which is what {@code +} emits — so the two spellings compute one value and are read as one term.
     * {@code divide} is absent: it answers a union rather than a number.
     */
    private static final Map<ValueName, Ast.BinOp> OPERATOR_CALLS = Map.of(
            op("Int.add"), Ast.BinOp.ADD,
            op("Int.subtract"), Ast.BinOp.SUB,
            op("Int.multiply"), Ast.BinOp.MUL,
            op("Decimal.add"), Ast.BinOp.ADD,
            op("Decimal.subtract"), Ast.BinOp.SUB,
            op("Decimal.multiply"), Ast.BinOp.MUL);

    /** The operations over two numbers that are the function form of no operator: the language
     * writes no {@code min}, {@code max}, {@code floorMod} or {@code compare}, so there is no second
     * spelling for a term to be read as one of. */
    static final Set<ValueName> NOT_AN_OPERATOR = Set.of(
            op("Int.min"), op("Int.max"), op("Int.floorMod"), op("Int.compare"),
            op("Decimal.min"), op("Decimal.max"));

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool.not");

    /** The operations each table has a rule for. What is asked of them is {@link Question}'s to
     * settle; these are so it can hold a rule to being one an operation is asked for. */
    static Set<ValueName> builtOperations() {
        return Bound.BUILDINGS.keySet();
    }

    static Set<ValueName> carryingOperations() {
        return Bound.CARRIERS.keySet();
    }

    /**
     * The kinds of container the library builds, each with the shape the building has — {@code
     * "List.SUBSET"}, {@code "Map.MAPS"}.
     *
     * <p>For the test that holds a carrying rule to every shape. A shape no construction of a kind
     * has is a cell no program can be written for, and which cells those are is the library's to say:
     * a set holds its elements in no order, so nothing permutes one, and that stops being true the day
     * an operation says otherwise. Read off the building table, whose every row already answers to a
     * program that fires it.
     */
    static Set<String> constructionKinds() {
        Set<String> kinds = new LinkedHashSet<>();
        Bound.BUILDINGS.forEach((operation, built) -> {
            Prelude.PreludeEntry entry = Prelude.entry(operation.name());
            String kind = entry == null ? null : kindOf(entry.signature().result());
            if (kind != null) {
                kinds.add(kind + "." + built.shape());
            }
        });
        return kinds;
    }

    /** What a container type is a container of, as the namespace its operations are written under. */
    private static String kindOf(Type built) {
        if (built instanceof Type.ListOf) {
            return "List";
        }
        if (built instanceof Type.SetOf) {
            return "Set";
        }
        return built instanceof Type.MapOf ? "Map" : null;
    }

    static Set<ValueName> emptinessChecks() {
        return EMPTINESS.keySet();
    }

    static Set<ValueName> quantifiers() {
        return QUANTIFIERS;
    }

    static Set<ValueName> projections() {
        return Bound.PROJECTIONS.keySet();
    }

    static Set<ValueName> sizeCalls() {
        return SIZE_CALLS;
    }

    static Set<ValueName> operatorForms() {
        return OPERATOR_CALLS.keySet();
    }

    /** Those of them the building table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> builtNames() {
        Set<String> names = new LinkedHashSet<>();
        builtOperations().forEach(operation -> names.add(operation.name()));
        return names;
    }

    /**
     * The tables, held to the declarations they were written for.
     *
     * <p>A row names an argument of an operation, and what an operation's arguments are is the
     * library's to say. Where the two disagree there is nothing to be done at a call — the rule is
     * about an argument that is not there, or is not the kind of thing the rule is about — so it is
     * said here, once, before any call is read, rather than met as a missing answer at whichever
     * reader arrives first.
     *
     * <p>Every row of every table, not the row a call happens to reach: a rule that disagrees with a
     * declaration is wrong whether or not a program calls it, and finding out when one does is the
     * same silence deferred.
     *
     * <p>Read on the first ask and not before, as {@link Combinators} and {@link Preserved} are: what
     * this requires of the library is required of a check that reads these rules, and a checker that
     * reads none must not be held to it.
     */
    private static final class Bound {

        private static final Map<ValueName, Built> BUILDINGS =
                bind(BUILT_FROM, Built::from, CONTAINER, Question::holdsElements,
                        "the container something is built from");
        private static final Map<ValueName, Carried> CARRIERS =
                bind(CARRIED, Carried::container, CONTAINER, Question::holdsElements,
                        "the container a predicate reads");
        private static final Map<ValueName, Reads> PROJECTIONS =
                bind(PROJECTION_OF, Function.identity(), CLOSURE, t -> t instanceof Type.FnOf,
                        "the projection a predicate is stated over");
    }

    /**
     * {@code rules}, once every row has been held to the operation it is about: the operation is one
     * the library declares, the argument it names is one that declaration has, and what stands there
     * is what the rule is about. A row naming a part of something the signature says the operation
     * does not hand is caught by {@link Reads}; one that writes a position the signature already
     * answers is caught here, since two answers to one question are what come apart later.
     */
    static <T> Map<ValueName, T> bind(Map<ValueName, T> rules, Function<T, Reads> reads,
                                      Reads derived, Predicate<Type> required, String what) {
        rules.forEach((operation, rule) -> {
            Prelude.PreludeEntry entry = Prelude.entry(operation.name());
            if (entry == null) {
                throw new IllegalStateException("a rule about " + what + " is written for "
                        + operation.name() + ", which the library does not declare");
            }
            List<Type> params = entry.signature().params();
            Reads at = reads.apply(rule);
            int position = at.positionIn(operation);
            if (position < 0 || position >= params.size()) {
                throw new IllegalStateException(operation.name() + " takes " + params.size()
                        + " argument(s), and the rule about " + what + " reads argument "
                        + (position + 1));
            }
            if (!required.test(params.get(position))) {
                throw new IllegalStateException("argument " + (position + 1) + " of "
                        + operation.name() + " is not " + what);
            }
            if (at instanceof Reads.At && Combinators.of(operation) != null
                    && derived.positionIn(operation) == position) {
                throw new IllegalStateException("the rule about " + what + " for " + operation.name()
                        + " writes the argument its signature already answers — say which part it is"
                        + " rather than where, so the two cannot come apart");
            }
        });
        return rules;
    }

    /** The container {@code call} built its result from, or null where the check has no rule about
     * what the operation keeps. */
    static Source builtFrom(Core.PreservedCall call) {
        Built built = Bound.BUILDINGS.get(call.operation());
        return built == null ? null : new Source(built.from().of(call), built.shape());
    }

    /** Where {@code call} reads the container it states its predicate of, or null where it is not a
     * predicate this carries anywhere. */
    static Carrying carried(Core.PreservedCall call) {
        Carried carried = Bound.CARRIERS.get(call.operation());
        return carried == null ? null : new Carrying(call, carried.container(), carried.through());
    }

    /** The projection {@code call}'s predicate is stated over, or null where it is stated over the
     * element itself — or where what stands in that argument is not a block this can read. */
    static Projection projectionOf(Core.PreservedCall call, Denotations at) {
        Reads reads = Bound.PROJECTIONS.get(call.operation());
        if (reads == null) {
            return null;
        }
        Core.Block projection = Terms.blockOf(reads.of(call), at);
        return projection == null ? null : new Projection(call, reads, projection);
    }

    static boolean isSize(ValueName operation) {
        return SIZE_CALLS.contains(operation);
    }

    static boolean isQuantifier(ValueName operation) {
        return QUANTIFIERS.contains(operation);
    }

    /** The size call an emptiness check means, or null where {@code operation} is not one. */
    static ValueName sizeMeantBy(ValueName operation) {
        return EMPTINESS.get(operation);
    }

    /** The operator {@code operation} is, where it is one written as a function, else null. */
    static Ast.BinOp operator(ValueName operation) {
        return OPERATOR_CALLS.get(operation);
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render
     * it. */
    static boolean readsAsATerm(ValueName operation) {
        return isSize(operation) || builtOperations().contains(operation)
                || carryingOperations().contains(operation) || isQuantifier(operation)
                || NOT.equals(operation);
    }

    /** The one container {@code e} asks the size of, or null where it is not a size call over one
     * argument. Asked rather than tested, so no reader spells the shape of a size call itself. */
    static Core sizeArgOf(Core e) {
        return e instanceof Core.PreservedCall call && isSize(call.operation())
                && call.args().size() == 1 ? call.args().get(0) : null;
    }

    /** The container a size is really the size of: an operation that keeps the size of what it was
     * built from is peeled away, so {@code List.length(List.map(f, xs))} is the atom
     * {@code List.length(xs)}. How the elements are made has no bearing on how many there are, which
     * is why the closure does not enter the key. */
    static Core sizeSource(Core e) {
        if (e instanceof Core.PreservedCall call) {
            Source built = builtFrom(call);
            if (built != null && built.shape().keepsSize()) {
                return sizeSource(built.container());
            }
        }
        return e;
    }

    private DischargeRules() {}
}
