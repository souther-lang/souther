package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation), and what each guarantees of what it answers
 * (spec §invariant-discharge-guarantees).
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
 * <p>A rule answers a call, not a position in one. Which argument it reads is written as {@link ArgumentRef}
 * and settled here, so no reader turns a number back into an argument and none has to ask whether the
 * number was one this call has. What makes that safe is the binding below: every row is held to the
 * declaration it was written for before any of them is read.
 */
final class DischargeRules {

    /** The operation {@code name} of the library module published as {@code alias}, as what a name
     * reaching it denotes. Written as the two values it is, so that a row here says which library it
     * is about without a reader splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
    }

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two.
     *
     * <p>Shared with the partition, which draws a boundary on the same calls ({@link
     * NumericMeasures}). Two lists would let a rule be discharged here and reported as one the model
     * does not state there. */
    private static final Set<ValueName> SIZE_CALLS = NumericMeasures.calls();

    /**
     * What a construction of a container keeps of the elements of the container it was built from.
     *
     * <ul>
     * <li>{@code PERMUTES} — the same elements in another order. Everything survives.
     * <li>{@code SUBSET} — some of the same elements. Nothing new is there, so a property of every
     *     element survives.
     * <li>{@code MAPS} — one new element for each. Nothing is known of what they are.
     * <li>{@code COLLAPSES} — at most one new element for each. Neither the elements nor what a
     *     closure that answers about them said.
     * </ul>
     *
     * <p>How many there are is {@link Cardinality} and is stated beside this, not read off it. The
     * two agree for every construction here — the same elements in another order is as many, some of
     * them is no more — and that agreement is what made one enum look like enough. It ends at a
     * construction given two containers: {@code List.append(a, b)} holds neither {@code a}'s elements
     * alone nor {@code b}'s, and its size is still no less than either. A statement about the count
     * that has to be spelled as a statement about the elements cannot be made there.
     */
    enum Shape {
        PERMUTES, SUBSET, MAPS, COLLAPSES
    }

    /**
     * How the size of a construction's result relates to the size of the container it was built from.
     *
     * <ul>
     * <li>{@code SAME} — exactly as many. Not stated as a fact: both are one atom, since
     *     {@link #sizeSource} answers the size of the result with the size of its source.
     * <li>{@code AT_MOST} — no more, and possibly fewer.
     * </ul>
     */
    enum Cardinality {
        SAME, AT_MOST
    }

    /** The argument the signature already says the elements come from, where the operation takes a
     * closure at all — so a rule about such an operation writes no position of its own. */
    private static final ArgumentRef CONTAINER = new ArgumentRef.TheContainer();

    /** The closure itself, for a rule stated over what the closure answers. */
    private static final ArgumentRef CLOSURE = new ArgumentRef.TheClosure();

    /** The argument at {@code position}, for an operation whose signature does not say which one it
     * is: one that takes no closure, or one given two containers. */
    private static ArgumentRef at(int position) {
        return new ArgumentRef.At(position);
    }

    /**
     * Where a container's elements came from, and how many of them the result has.
     *
     * <p>The lineage is what is declared; {@link #shape} is read off it. The two are not the same
     * statement and the shape is the coarser — {@code List.filterMap} and {@code Set.map} are one
     * shape and two lineages — so declaring the shape and deriving the lineage would be deriving
     * what was thrown away. Written this way round, a reader that wants where an element came from
     * asks {@link ElementLineage} and a reader that wants whether a property survives asks here,
     * and neither is recovering the other's answer.
     */
    record Built(List<ElementLineage.OutputLineage> outputs, Cardinality size) {

        Built {
            outputs = List.copyOf(outputs);
            if (outputs.isEmpty()) {
                throw new IllegalArgumentException("a construction answers somewhere");
            }
        }

        /** The one place its elements stand, for a rule about an operation that answers one run of
         *  them. */
        Built(ElementLineage lineage, Cardinality size) {
            this(List.of(new ElementLineage.OutputLineage(
                    ElementLineage.ResultPath.elements(), lineage)), size);
        }

        /** Where its elements came from, where they all came from one place. */
        ElementLineage lineage() {
            if (outputs.size() != 1) {
                throw new IllegalStateException(
                        "a construction answering more than one run of elements was asked for one"
                                + " lineage: " + outputs);
            }
            return outputs.get(0).origin();
        }

        /** Which argument it was built from, where one argument is what it was built from. */
        ArgumentRef from() {
            ElementLineage.Source source = lineage().source();
            if (source == null) {
                throw new IllegalStateException(
                        "a construction whose elements come from more than one place was asked which"
                                + " one: " + outputs);
            }
            return source.argument();
        }

        /**
         * What the building keeps of the elements it was built from, in the words the discharge
         * check is written in.
         *
         * <p>A projection and the one place it happens. What survives a construction is decided by
         * whether the elements are the source's own and by whether there are as many of them, and
         * both of those are stated above — so the four words are a reading of the pair rather than
         * a fifth thing to keep in step with it.
         */
        Shape shape() {
            boolean asMany = size == Cardinality.SAME;
            return switch (lineage()) {
                case ElementLineage.SameAs _ -> asMany ? Shape.PERMUTES : Shape.SUBSET;
                case ElementLineage.ClosureResult _ -> asMany ? Shape.MAPS : Shape.COLLAPSES;
                // What the closure answered holds it, so what was stated of the source says nothing
                // of it, and there may be any number of them. No word of the four is about that,
                // and the nearest is the one for elements nothing was kept of.
                case ElementLineage.InsideClosureResult _ -> Shape.COLLAPSES;
                case ElementLineage.OneOf _ -> throw new IllegalStateException(
                        "a construction whose elements come from more than one place has no single"
                                + " source for a shape to be about: " + outputs);
            };
        }
    }

    /** The container {@code call} built its result from, and what the building kept of it. */
    record Source(Core container, Shape shape, Cardinality size) {}

    private static final Map<ValueName, Built> BUILT_FROM = Map.ofEntries(
            Map.entry(op("List", "reverse"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.SAME)),
            Map.entry(op("List", "sort"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.SAME)),
            Map.entry(op("List", "sortBy"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.SAME)),
            Map.entry(op("List", "map"), new Built(new ElementLineage.ClosureResult(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.SAME)),
            Map.entry(op("List", "mapIndexed"), new Built(new ElementLineage.ClosureResult(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.SAME)),
            Map.entry(op("Map", "mapValues"), new Built(new ElementLineage.ClosureResult(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.SAME)),
            Map.entry(op("List", "filter"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)),
            Map.entry(op("List", "distinct"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.AT_MOST)),
            Map.entry(op("List", "take"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(1), 1)), Cardinality.AT_MOST)),
            Map.entry(op("List", "drop"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(1), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Set", "filter"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)),
            Map.entry(op("Map", "filterEntries"),
                    new Built(new ElementLineage.SameAs(
                            new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)),
            Map.entry(op("List", "distinctBy"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)),
            Map.entry(op("Map", "remove"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(1), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Set", "remove"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(1), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Map", "intersection"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Map", "difference"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Set", "intersection"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Set", "difference"), new Built(new ElementLineage.SameAs(
                    new ElementLineage.Source(at(0), 1)), Cardinality.AT_MOST)),
            Map.entry(op("Map", "updateIfPresent"), new Built(new ElementLineage.ClosureResult(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.SAME)),
            // Inside what the closure answered, which is an optional here and a list in a
            // `flatMap`. One lineage for the two, told apart by what the closure's own signature
            // says it answers with.
            Map.entry(op("List", "filterMap"),
                    new Built(new ElementLineage.InsideClosureResult(
                            new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)),
            Map.entry(op("Set", "map"), new Built(new ElementLineage.ClosureResult(
                    new ElementLineage.Source(CONTAINER, 1)), Cardinality.AT_MOST)));

    /**
     * The containers a construction's result is never smaller than.
     *
     * <p>Written on its own and not as a {@link Shape}, because none of these establishes an element
     * relation to a single source that a shape states. It is not that they keep nothing:
     * {@code List.append(a, b)} keeps every element of both, and holds neither {@code a}'s alone nor
     * {@code b}'s, so neither of the two is what it was built from; an insert puts in an element or
     * an entry the container it read did not hold. The cardinality is a separate fact and survives
     * either way — which is why these sat among the constructions nothing is known of, their bound
     * discarded with an element rule that was never the same statement.
     *
     * <p>No more than the bound. A union answers one of what both sides hold and an insert of
     * something already there adds nothing, so neither answers the sum of what it read; appending
     * does, and stating it for that one alone would be a second rule for one operation. The bound is
     * what they share, and it is what a lower-bound invariant asks for.
     */
    private static final Map<ValueName, List<ArgumentRef>> NO_SMALLER_THAN = Map.of(
            op("List", "append"), List.of(at(0), at(1)),
            op("Set", "union"), List.of(at(0), at(1)),
            op("Map", "union"), List.of(at(0), at(1)),
            op("Set", "insert"), List.of(at(1)),
            op("Map", "insert"), List.of(at(2)));

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
     * still does, which is what a shape would have had to say. How many there are is said instead by
     * {@link #NO_SMALLER_THAN}, which those of them whose result is never smaller than a source it
     * names are in.
     *
     * <p>They answer the same elements in a container of another kind. That is true and unsayable:
     * every statement the check makes names the kind it is about — {@code List.length} and
     * {@code List.all}, or {@code Set.size} and {@code Set.contains} — so nothing said of the one is
     * a statement about the other, and a rule between them would carry nothing. A statement that
     * spans kinds is what would have to exist first.
     */
    static final Set<ValueName> NOTHING_KEPT = Set.of(
            op("Map", "keys"), op("Map", "toList"), op("Map", "fromList"), op("List", "groupBy"),
            op("List", "concat"), op("List", "zipShortest"), op("List", "flatMap"),
            op("Map", "insert"), op("Set", "insert"), op("Map", "union"), op("Set", "union"),
            op("List", "append"), op("Map", "updateOrInsert"),
            op("Map", "values"), op("Set", "toList"), op("Set", "fromList"), op("List", "indexBy"));

    /** Where a predicate reads its container, and which shapes of construction carry it there.
     * {@code List.all} holds of any sublist of a list it holds of; {@code List.contains} does not, and
     * neither survives a mapping — what a mapped element is, the mapping alone does not say. */
    record Carried(ArgumentRef container, Set<Shape> through) {}

    private static final Map<ValueName, Carried> CARRIED = Map.of(
            op("List", "all"), new Carried(CONTAINER, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List", "allDistinctBy"), new Carried(CONTAINER, Set.of(Shape.PERMUTES, Shape.SUBSET)),
            op("List", "any"), new Carried(CONTAINER, Set.of(Shape.PERMUTES)),
            op("List", "contains"), new Carried(at(1), Set.of(Shape.PERMUTES)),
            op("Set", "contains"), new Carried(at(1), Set.of(Shape.PERMUTES)),
            op("Map", "containsKey"), new Carried(at(1), Set.of(Shape.PERMUTES)));

    /** Where a predicate reads its container at a call, and how far its statement travels. */
    record Carrying(Core.PreservedCall stated, ArgumentRef at, Set<Shape> through) {

        Core container() {
            return at.of(stated);
        }

        /** {@code call} — a call to the same operation — with the container it reads replaced. */
        Core.PreservedCall over(Core.PreservedCall call, Core container) {
            if (!call.operation().equals(stated.operation())) {
                throw new IllegalStateException("a rule read for " + stated.operation()
                        + " was asked to rewrite a call to " + call.operation());
            }
            return at.replacedIn(call, container);
        }
    }

    /** Where a predicate reads the projection it is stated over. A mapping keeps a projection when
     * the closure copies that field from the element unchanged, so the predicate holds of the mapped
     * list exactly when it holds of what was mapped, over the field it came from. */
    private static final Map<ValueName, ArgumentRef> PROJECTION_OF =
            Map.of(op("List", "allDistinctBy"), CLOSURE);

    /** The projection a predicate at a call is stated over, as the block it answers with. */
    record Projection(Core.PreservedCall stated, ArgumentRef at, Core.Block projection) {

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
    private static final Set<ValueName> QUANTIFIERS = Set.of(op("List", "all"));

    /** Emptiness, by the size call it means. This is not a rule about what an operation does to a
     * property but about what a predicate <em>says</em>: {@code List.isEmpty(xs)} and
     * {@code List.length(xs) == 0} are one statement, so a guard writing either discharges a clause
     * writing the other. Without it the two would be unrelated, which is an accident of which one the
     * author reached for. */
    private static final Map<ValueName, ValueName> EMPTINESS = Map.of(
            op("List", "isEmpty"), op("List", "length"),
            op("Set", "isEmpty"), op("Set", "size"),
            op("Map", "isEmpty"), op("Map", "size"),
            op("String", "isEmpty"), op("String", "length"));

    /** The predicates whose statement this carries nowhere. A predicate over a string states
     * something of the characters it holds in the order it holds them, and what would carry such a
     * statement is a construction of a container from a container — which a string is not one of,
     * its length being all this names of it. An emptiness check states a size, which travels as a
     * size does ({@link #EMPTINESS}) and not as a property of elements. */
    static final Set<ValueName> NOTHING_CARRIED = Set.of(
            op("String", "contains"), op("String", "startsWith"), op("String", "endsWith"),
            op("String", "matches"),
            op("List", "isEmpty"), op("Set", "isEmpty"), op("Map", "isEmpty"), op("String", "isEmpty"));

    /** The predicates of a single container that are not emptiness checks. The library has none:
     * every one-argument predicate it declares over a container or a string is one, and one that was
     * not would be named here with what it says instead. */
    static final Set<ValueName> NOT_AN_EMPTINESS_CHECK = Set.of();

    /** The predicates that apply a predicate to what a container holds without stating it of every
     * element. {@code List.any} states it of some, so what it says of the container says nothing
     * about the element a closure is handed. */
    static final Set<ValueName> NOT_A_QUANTIFIER = Set.of(op("List", "any"));

    /** The predicates that compute something other than a truth value from each element and are not
     * stated over it. The library has none: {@code allDistinctBy} is the only such predicate and its
     * projection is its closure's answer. */
    static final Set<ValueName> NOT_STATED_OVER_A_PROJECTION = Set.of();

    /** The numbers answered about a container that are not one of its sizes. The library has none:
     * every {@code Int} it answers about a container is how many it holds. */
    static final Set<ValueName> NOT_A_SIZE = Set.of();

    /**
     * What has to hold of the arguments before a bound on the result does.
     *
     * <p>Of the arguments and of nothing else. A condition the path establishes is what the arguments
     * are known to be at one call, and a rule resting on one would hold where a guard was written and
     * not where the operation was — which is a statement about the program rather than about the
     * operation.
     */
    sealed interface Provided {

        /** Whether {@code call} is one this rule holds at. */
        boolean holdsAt(Core.PreservedCall call, java.util.function.Function<Core, BigDecimal> folded);

        /** Nothing: the bound is what the operation does, whatever it is given. */
        record Always() implements Provided {
            @Override
            public boolean holdsAt(Core.PreservedCall call,
                                   java.util.function.Function<Core, BigDecimal> folded) {
                return true;
            }
        }

        /**
         * An argument that reads as a constant above zero.
         *
         * <p>Constant, and not written as one. What a name was given is what the name is, here as
         * everywhere else the check reads a value ({@link Terms#affineOf}), so {@code floorMod(x, k)}
         * under {@code let k = 100} is the same call as {@code floorMod(x, 100)} — one spelling of a
         * value the check has already read. Requiring the digits at the call would make a rule the
         * author cannot predict from what the value is, only from where it was written.
         */
        record ConstantAboveZero(ArgumentRef argument) implements Provided {
            @Override
            public boolean holdsAt(Core.PreservedCall call,
                                   java.util.function.Function<Core, BigDecimal> folded) {
                BigDecimal at = folded.apply(argument.of(call));
                return at != null && at.signum() > 0;
            }
        }
    }

    /**
     * One bound an operation's result has, as the domain holds bounds: the result against a constant,
     * or the result against one argument and a constant.
     *
     * <p>The shape is the domain's ({@link NumericDomain}) and is what a row may say. A rule of
     * another shape — a result between two arguments, a result no greater than a sum — is one the
     * domain would take in and derive nothing from, so it is not writable here rather than written
     * and silently dropped.
     *
     * @param against  the argument the result is bounded against, or null where the bound is a
     *                 constant one
     * @param offset   added to that argument, or the constant itself where there is no argument
     * @param rel      how the result stands to it
     * @param provided what has to hold of the arguments for this to be the operation's answer
     */
    record ResultBound(ArgumentRef against, BigDecimal offset, Rel rel, Provided provided) {}

    /** {@code result rel n}. */
    private static ResultBound resultIs(Rel rel, long n) {
        return new ResultBound(null, BigDecimal.valueOf(n), rel, new Provided.Always());
    }

    /** The same, where the operation answers that only under a condition on its arguments. */
    private static ResultBound resultIs(Rel rel, long n, Provided provided) {
        return new ResultBound(null, BigDecimal.valueOf(n), rel, provided);
    }

    /** {@code result rel argument + offset}. */
    private static ResultBound resultIs(Rel rel, ArgumentRef argument, long offset, Provided provided) {
        return new ResultBound(argument, BigDecimal.valueOf(offset), rel, provided);
    }

    /**
     * What holds of an operation's result wherever the call is written.
     *
     * <p>Each row is a fact about the operation, so it is stated at every call and not only where
     * something was guarded: {@code Int.abs(x)} is not negative whatever {@code x} is. That is the
     * same kind of statement {@link Predicates#sizeFacts} already makes of every size call it walks
     * past, and it is read the same way — asserted into the domain where a clause is read and where a
     * condition is assumed alike.
     *
     * <p>{@code Int.floorMod} states both its ends only where the divisor reads as a constant above
     * zero, and neither of them otherwise. The result takes the sign of the divisor — {@code
     * floorMod(1, -3)} is {@code -2} — so a divisor that could be negative puts it the other side of
     * zero, and the lower end is as much the divisor's to decide as the upper one. A divisor the
     * check cannot read bounds it nowhere. Its {@code 0} is not a case at all: the operation aborts.
     *
     * <p>{@code Decimal.toInt} is within one of what it rounds, whichever mode it is handed. What a
     * single mode does more narrowly — {@code HALF_UP} rounds to within a half — is a second rule and
     * is not stated here, since the mode is an argument this reads nothing of.
     */
    private static final Map<ValueName, List<ResultBound>> BOUNDS_ON_THE_RESULT = Map.of(
            op("Int", "abs"), List.of(resultIs(Rel.GE, 0)),
            op("Decimal", "abs"), List.of(resultIs(Rel.GE, 0)),
            op("Int", "floorMod"), List.of(
                    resultIs(Rel.GE, 0, new Provided.ConstantAboveZero(at(1))),
                    resultIs(Rel.LT, at(1), 0, new Provided.ConstantAboveZero(at(1)))),
            op("Decimal", "toInt"), List.of(
                    resultIs(Rel.GT, at(1), -1, new Provided.Always()),
                    resultIs(Rel.LT, at(1), 1, new Provided.Always())));

    /**
     * The operations answering a number this bounds nothing of, in two groups.
     *
     * <p>Their result is not bounded by their arguments at all. The arithmetic and its function forms
     * answer a number that may be anywhere, and what relates it to the operands is that it <em>is</em>
     * the operands' arithmetic, which a term already reads ({@link #OPERATOR_CALLS}). A comparison
     * answers a sign, and what that sign says is the order it decides ({@link #ORDERS}) rather than a
     * range it lies in.
     *
     * <p>Their result is one of the arguments, decided by the arguments. A bound on such a result is
     * what {@link #CHOOSES} derives from the case it is in — stating it here as well would be one
     * operation answering to two tables, and the two would come apart the day the library changes
     * which argument it answers.
     *
     * <p>{@code Decimal.round} answers a value at another scale, which is a bound of a shape a row
     * cannot state: how far it moved depends on the scale it was handed. {@code Decimal.fromInt}
     * answers the number it was given, which {@link #ANSWERS_ITS_ARGUMENT} states as the stronger
     * thing it is — the two values are one, not one within reach of the other.
     */
    static final Set<ValueName> BOUNDS_NOTHING = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"),
            op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
            op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp"),
            op("Decimal", "fromInt"), op("Decimal", "round"));

    /**
     * How far an operation moved the value it was given, stated through the measure that counts two
     * such values apart: {@code measure(of, result) == per · amount}.
     *
     * <p>The statement a shift makes is not a bound on what it answers — a date is not a number — so
     * it is written in the one language the check has about such values, which is the number a
     * measure answers of two of them. That number is what an invariant over a pair of dates is
     * written in as well, so the rule and the clause meet without either being rewritten.
     *
     * @param measure the library's operation counting the two apart, in the order {@code (of, result)}
     * @param of      the argument the result was shifted from
     * @param amount  the argument saying by how much
     * @param per     how many of what the measure counts one of {@code amount} is
     */
    record Shift(ValueName.Stdlib measure, ArgumentRef of, ArgumentRef amount, BigDecimal per) {}

    private static Shift shifts(String module, String measure, ArgumentRef of, ArgumentRef amount, long per) {
        return new Shift(new ValueName.Stdlib(module, measure), of, amount,
                BigDecimal.valueOf(per));
    }

    /**
     * The operations that move a value by an amount, each with what it did stated through a measure.
     *
     * <p>Every one of them works on a local value, where a day is a day and an hour is sixty
     * minutes ({@code Temporals}), so what each states is exact rather than usually true.
     *
     * <p>{@code Date.addMonths} and {@code Date.addYears} are not here and are not oversights: months
     * and years hold different numbers of days, so neither states a count of the one measure a pair
     * of dates has. What a path knows of such a shift — that a later month is not earlier — is
     * something else, and follows from what is known of the arguments rather than from the operation.
     */
    private static final Map<ValueName, Shift> SHIFTS = Map.of(
            op("Date", "addDays"), shifts("Date", "daysBetween", at(1), at(0), 1),
            op("DateTime", "addMinutes"), shifts("DateTime", "minutesBetween", at(1), at(0), 1),
            op("DateTime", "addHours"), shifts("DateTime", "minutesBetween", at(1), at(0), 60),
            op("DateTime", "addDays"), shifts("DateTime", "minutesBetween", at(1), at(0), 1440));

    /** The operations that move a value by an amount the measures this has cannot count. A month and
     * a year are not a fixed number of days, so a date shifted by either stands at a distance no rule
     * here can write. */
    static final Set<ValueName> SHIFTS_BY_NOTHING_MEASURABLE = Set.of(
            op("Date", "addMonths"), op("Date", "addYears"));

    /** A relation between two arguments: {@code left rel right}. What a case of a piecewise
     * definition is reached under, written in the arguments the operation was given and in nothing
     * else. */
    record ArgumentsStand(ArgumentRef left, Rel rel, ArgumentRef right) {}

    private static ArgumentsStand where(ArgumentRef left, Rel rel, ArgumentRef right) {
        return new ArgumentsStand(left, rel, right);
    }

    /** One case of an operation's definition: the argument it answers there, and what holds of the
     * arguments where it does. */
    record Choice(ArgumentRef answers, List<ArgumentsStand> given) {}

    private static Choice answers(ArgumentRef argument, ArgumentsStand... given) {
        return new Choice(argument, List.of(given));
    }

    /**
     * An operation's definition, as the cases it is written in.
     *
     * <p>The list is exhaustive: the conditions of its cases cover everything the operation can be
     * given, so what holds in every case holds of the result. That is the whole of what makes a
     * reading of these sound, and it is a claim about the list rather than about any row in it — a
     * case left out does not make the others wrong, it makes a clause provable that the values can
     * fail. So the cases are written as the library writes them, in the order it writes them, and
     * each is held to a program that reaches it.
     */
    record Choices(List<Choice> cases) {}

    private static Choices choices(Choice... cases) {
        return new Choices(List.of(cases));
    }

    /**
     * The operations that answer one of the values they were given, as the cases they are defined in.
     *
     * <p>Each is the library's own definition read back: {@code min(a, b)} is {@code a} where
     * {@code a < b} and {@code b} otherwise, and {@code clamp(lo, hi, n)} is written as a chain of
     * two conditions, so the second and third cases carry the denial of what stands before them.
     * Carrying it is not tidiness — {@code clamp} does not ask that {@code lo} be below {@code hi},
     * and where it is not, the case that answers {@code hi} is reached with {@code n} above
     * {@code lo}. A rule that said the result is between the two would prove a clause the values
     * fail.
     *
     * <p>Stated here rather than as bounds on the result ({@link #BOUNDS_ON_THE_RESULT}) because
     * what these answer depends on the arguments, and a bound that does not may not be written for
     * them. The bounds a case gives — a smaller of two is no greater than either — follow from the
     * case and are derived where a clause is read, so they are not a second table to keep in step
     * with this one.
     */
    private static final Map<ValueName, Choices> CHOOSES = Map.of(
            op("Int", "min"), choices(
                    answers(at(0), where(at(0), Rel.LT, at(1))),
                    answers(at(1), where(at(0), Rel.GE, at(1)))),
            op("Decimal", "min"), choices(
                    answers(at(0), where(at(0), Rel.LT, at(1))),
                    answers(at(1), where(at(0), Rel.GE, at(1)))),
            op("Int", "max"), choices(
                    answers(at(0), where(at(0), Rel.GT, at(1))),
                    answers(at(1), where(at(0), Rel.LE, at(1)))),
            op("Decimal", "max"), choices(
                    answers(at(0), where(at(0), Rel.GT, at(1))),
                    answers(at(1), where(at(0), Rel.LE, at(1)))),
            op("Int", "clamp"), choices(
                    answers(at(0), where(at(2), Rel.LT, at(0))),
                    answers(at(1), where(at(2), Rel.GE, at(0)), where(at(2), Rel.GT, at(1))),
                    answers(at(2), where(at(2), Rel.GE, at(0)), where(at(2), Rel.LE, at(1)))),
            op("Decimal", "clamp"), choices(
                    answers(at(0), where(at(2), Rel.LT, at(0))),
                    answers(at(1), where(at(2), Rel.GE, at(0)), where(at(2), Rel.GT, at(1))),
                    answers(at(2), where(at(2), Rel.GE, at(0)), where(at(2), Rel.LE, at(1)))));

    /**
     * The operations answering a number that answer none of their arguments back, in three groups.
     *
     * <p>They compute a new number. The arithmetic and its function forms are this: what
     * {@code a + b} answers is neither {@code a} nor {@code b}, whatever they are.
     *
     * <p>They answer something about the arguments. {@code compare} answers a sign, {@code floorMod}
     * a remainder, {@code abs} a distance, {@code toInt} the whole number a value rounds to, and
     * {@code round} a value at another scale — none of which is one of the values handed in, though
     * each of the last four is one where the argument already had that shape. That the answer
     * <em>can</em> be an argument is not what this asks: a case is one the operation is defined by,
     * and reading a coincidence as a case would state a condition the definition does not have.
     *
     * <p>{@code Decimal.fromInt} answers the number it was given in another type, which
     * {@link #ANSWERS_ITS_ARGUMENT} states unconditionally. A case would put a condition on a
     * statement that has none.
     */
    static final Set<ValueName> CHOOSES_NOTHING = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"), op("Int", "floorMod"),
            op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"), op("Decimal", "round"),
            op("Decimal", "fromInt"));

    /**
     * The operations whose result is the number an argument already is, and which argument that is.
     *
     * <p>Such a call is read into the form its argument has rather than given an atom of its own, so
     * a guard about the argument settles a clause about the call. {@code Decimal.fromInt(n)} is the
     * one the library has: every {@code Int} is a {@code Decimal} exactly, and the widening states
     * nothing of its own.
     *
     * <p>Not a choice among arguments ({@link #CHOOSES}). What a choice answers is one of two values,
     * decided by the arguments, and which one it is has to be reasoned about case by case; this
     * answers one value unconditionally, in another type. Reading the second as a choice with one
     * candidate would put every value-preserving conversion under a table about selection, and the
     * two stop being one question the moment the library gains a conversion that is not a widening.
     */
    private static final Map<ValueName, ArgumentRef> ANSWERS_ITS_ARGUMENT =
            Map.of(op("Decimal", "fromInt"), at(0));

    /**
     * The operations answering a number from a number that answer none of them back, in three groups.
     *
     * <p>They compute a new number from their operands. The arithmetic and its function forms are
     * this, and what they answer is already read as arithmetic over the operands themselves
     * ({@link #OPERATOR_CALLS}) rather than as one of them.
     *
     * <p>They answer something about the arguments rather than one of them: {@code compare} a sign,
     * {@code floorMod} a remainder, {@code abs} a distance with the sign dropped, {@code toInt} the
     * whole number a value rounds to, {@code round} a value at another scale. What such a result is
     * bounded by is {@link #BOUNDS_ON_THE_RESULT}, which is a different statement from being a value
     * that was already there.
     *
     * <p>They answer one of their arguments, and which one depends on the arguments. That is
     * {@link #CHOOSES}, and a rule that dropped the condition would say {@code Int.min(a, b)} is
     * {@code a}.
     */
    static final Set<ValueName> ANSWERS_NO_ARGUMENT_OF_ITS_OWN = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Decimal", "add"), op("Decimal", "subtract"), op("Decimal", "multiply"),
            op("Int", "compare"), op("Decimal", "compare"), op("Int", "floorMod"),
            op("Int", "abs"), op("Decimal", "abs"), op("Decimal", "toInt"), op("Decimal", "round"),
            op("Int", "min"), op("Int", "max"), op("Int", "clamp"),
            op("Decimal", "min"), op("Decimal", "max"), op("Decimal", "clamp"));

    /**
     * The library's function forms of the arithmetic operators, and the operator each one is. They
     * reach the same kernel in the same argument order — {@code Int.add} is {@code IntMath.addExact},
     * which is what {@code +} emits — so the two spellings compute one value and are read as one term.
     * {@code divide} is absent: it answers a union rather than a number.
     */
    private static final Map<ValueName, BinOp> OPERATOR_CALLS = Map.of(
            op("Int", "add"), BinOp.ADD,
            op("Int", "subtract"), BinOp.SUB,
            op("Int", "multiply"), BinOp.MUL,
            op("Decimal", "add"), BinOp.ADD,
            op("Decimal", "subtract"), BinOp.SUB,
            op("Decimal", "multiply"), BinOp.MUL);

    /** The operations over two numbers that are the function form of no operator: the language
     * writes no {@code min}, {@code max}, {@code floorMod} or {@code compare}, so there is no second
     * spelling for a term to be read as one of. */
    static final Set<ValueName> NOT_AN_OPERATOR = Set.of(
            op("Int", "min"), op("Int", "max"), op("Int", "floorMod"), op("Int", "compare"),
            op("Decimal", "min"), op("Decimal", "max"));

    /**
     * Which of the two arguments a positive answer names as the greater. That is the whole of what a
     * row of {@link #ORDERS} says, and it is two cases, so it is written as a type with two — not as
     * one of the language's operators, which would say the same thing in a type where most of the
     * values say nothing and the ones that do have to be agreed on somewhere else.
     *
     * <p>Each case carries the two positions itself, since which argument is the lesser is settled by
     * which is the greater and there is no reading where the two are chosen apart.
     */
    enum PositiveOrder {
        FIRST_ARGUMENT_GREATER(0, 1),
        SECOND_ARGUMENT_GREATER(1, 0);

        private final int greater;
        private final int lesser;

        PositiveOrder(int greater, int lesser) {
            this.greater = greater;
            this.lesser = lesser;
        }

        /** The argument of {@code call} a positive answer names as the greater. */
        Core greaterOf(Core.PreservedCall call) {
            return call.args().get(greater);
        }

        /** The other one. */
        Core lesserOf(Core.PreservedCall call) {
            return call.args().get(lesser);
        }
    }

    /**
     * The operations answering the order of their two arguments as the sign of a number, and which
     * argument a positive answer names as the greater. Zero states the equality, and a negative
     * answer the relation the other way, so one row is the whole of what such an operation says.
     *
     * <p>Which relation a guard writing one states then follows from where the sign stands against
     * zero and from nothing else, so the six relations and the two operand orders are one account
     * rather than twelve rows ({@link Predicates#asOrderComparison}). The direction is not the same
     * for all of them: {@code compare(a, b)} is positive where {@code a} is the greater, and
     * {@code daysBetween(from, to)} counts forward from its first argument, so it is positive where
     * the second one is.
     */
    private static final Map<ValueName, PositiveOrder> ORDERS = Map.of(
            op("Int", "compare"), PositiveOrder.FIRST_ARGUMENT_GREATER,
            op("Decimal", "compare"), PositiveOrder.FIRST_ARGUMENT_GREATER,
            op("Date", "daysBetween"), PositiveOrder.SECOND_ARGUMENT_GREATER);

    /**
     * The operations answering a number from two values of one type whose sign is not their order.
     *
     * <p>Arithmetic and a choice between two values are not orders at all: what {@code Int.subtract}
     * answers has the sign of one and says how far apart they are as well, which is what a term
     * already reads it as, and {@code min} answers one of the two rather than anything about the
     * pair. {@code DateTime.minutesBetween} is the one that has to be told apart: it counts whole
     * minutes, so a zero says the two are less than a minute apart rather than that they are equal,
     * and a non-negative count does not say the second is not the earlier. Its strict signs do state
     * the order, and a rule that holds for four of the six relations is not this one.
     */
    static final Set<ValueName> DECIDES_NO_ORDER = Set.of(
            op("Int", "add"), op("Int", "subtract"), op("Int", "multiply"),
            op("Int", "min"), op("Int", "max"), op("Int", "floorMod"),
            op("DateTime", "minutesBetween"));

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool", "not");

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
            Prelude.PreludeEntry entry = operation instanceof ValueName.Stdlib library
                    ? Prelude.entry(library.qualified()) : null;
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

    static Set<ValueName> orderings() {
        return ORDERS.keySet();
    }

    static Set<ValueName> formOperations() {
        return Bound.FORMS.keySet();
    }

    /** Those of them the read-through table has, by name, for the test that holds each to a
     * construction it discharges. */
    static Set<String> formNames() {
        Set<String> names = new LinkedHashSet<>();
        formOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> boundedOperations() {
        return Bound.BOUNDS.keySet();
    }

    static Set<ValueName> choosingOperations() {
        return Bound.CHOICES.keySet();
    }

    /** Those of them the choosing table has, by name, for the test that holds each case to a
     * program that reaches it. */
    static Set<String> choosingNames() {
        Set<String> names = new LinkedHashSet<>();
        choosingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> shiftingOperations() {
        return Bound.MEASURED.keySet();
    }

    /** Those of them the shifting table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> shiftingNames() {
        Set<String> names = new LinkedHashSet<>();
        shiftingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    /** What {@code e} states through a measure, or null where it is not a shift this has a rule
     * about. */
    static Shift shiftBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.MEASURED.get(call.operation()) : null;
    }

    /** The cases {@code e} is defined in, or null where it is not a call to an operation that
     * answers one of the values it was given. */
    static Choices chosenBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.CHOICES.get(call.operation()) : null;
    }

    /**
     * The bounding table's rows, by the name of the operation each is about — one entry per row, so
     * an operation bounded at both ends appears twice.
     *
     * <p>For the test that holds each row to a construction it discharges. By row and not by
     * operation: one program needs one of an operation's rows, so a set of names would be satisfied
     * by a rule that had been written for one end and never fired for the other.
     */
    static List<String> boundedRows() {
        List<String> rows = new ArrayList<>();
        Bound.BOUNDS.forEach((operation, bounds) ->
                bounds.forEach(bound -> rows.add(operation.toString())));
        return rows;
    }

    /**
     * The bounds {@code call}'s result has here: the operation's rows, less those whose condition on
     * the arguments this call does not meet.
     *
     * @param constant what an argument reads as, or null where it reads as no constant. Asked of the
     *                 caller because what a value is read as is the reading's answer and not a
     *                 property of the syntax at the call.
     */
    static List<ResultBound> boundsOn(Core.PreservedCall call,
                                      Function<Core, BigDecimal> constant) {
        List<ResultBound> rows = Bound.BOUNDS.get(call.operation());
        if (rows == null) {
            return List.of();
        }
        List<ResultBound> holding = new ArrayList<>(rows.size());
        for (ResultBound row : rows) {
            if (row.provided().holdsAt(call, constant)) {
                holding.add(row);
            }
        }
        return holding;
    }

    /** The argument whose number {@code e} answers, or null where it is not a call this reads as one
     * of its arguments. The value itself and not a term for it: what it is read as is the form the
     * argument already has, which is the caller's to build. */
    static Core answersItsArgument(Core e) {
        if (!(e instanceof Core.PreservedCall call)) {
            return null;
        }
        ArgumentRef reads = Bound.FORMS.get(call.operation());
        return reads == null ? null : reads.of(call);
    }

    /** Those of them the building table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> builtNames() {
        Set<String> names = new LinkedHashSet<>();
        builtOperations().forEach(operation -> names.add(operation.toString()));
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
     * <p>A numeric rule names no part of what an operation hands a closure, since such an operation
     * hands none, so it is bound with no derived position for a written one to be held against.
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
        private static final Map<ValueName, ArgumentRef> PROJECTIONS =
                bind(PROJECTION_OF, Function.identity(), CLOSURE, t -> t instanceof Type.FnOf,
                        "the projection a predicate is stated over");
        private static final Map<ValueName, List<ArgumentRef>> LOWER_BOUNDS =
                bindEach(NO_SMALLER_THAN, CONTAINER, Question::holdsElements,
                        "a container the result is no smaller than");
        private static final Map<ValueName, ArgumentRef> FORMS =
                bind(ANSWERS_ITS_ARGUMENT, Function.identity(), null, Question::isANumber,
                        "the argument whose number the result is");
        private static final Map<ValueName, List<ResultBound>> BOUNDS =
                bindBounds(BOUNDS_ON_THE_RESULT);
        private static final Map<ValueName, Choices> CHOICES = bindChoices(CHOOSES);
        private static final Map<ValueName, Shift> MEASURED = bindShifts(SHIFTS);
    }

    /**
     * As {@link #bind}, for a rule stating a shift through a measure: the amount is a number, the
     * value shifted is of the type the measure counts, and the measure counts two of what the
     * operation answers. A rule pairing an operation with a measure of something else would state a
     * relation between two values that have none.
     */
    private static Map<ValueName, Shift> bindShifts(Map<ValueName, Shift> rules) {
        rules.forEach((operation, shift) -> {
            bind(Map.of(operation, shift.amount()), Function.identity(), null, Question::isANumber,
                    "the amount a shift moves by");
            Prelude.PreludeEntry counts = Prelude.entry(shift.measure().qualified());
            if (counts == null) {
                throw new IllegalStateException("the rule about " + operation + " counts through "
                        + shift.measure().qualified() + ", which the library does not declare");
            }
            Prelude.PreludeEntry shifted = Prelude.entry(((ValueName.Stdlib) operation).qualified());
            List<Type> counted = counts.signature().params();
            if (counted.size() != 2 || !Question.isANumber(counts.signature().result())
                    || !counted.get(0).equals(shifted.signature().result())
                    || !counted.get(1).equals(shifted.signature().result())) {
                throw new IllegalStateException(shift.measure().qualified()
                        + " does not count two of what " + operation + " answers apart as a number");
            }
            bind(Map.of(operation, shift.of()), Function.identity(), null,
                    t -> t.equals(shifted.signature().result()),
                    "the value a shift moves from");
        });
        return rules;
    }

    /** As {@link #bind}, for the arguments a case names: the one it answers, and the two sides of
     * each condition it is reached under. */
    private static Map<ValueName, Choices> bindChoices(Map<ValueName, Choices> rules) {
        rules.forEach((operation, choices) -> choices.cases().forEach(choice -> {
            List<ArgumentRef> named = new ArrayList<>();
            named.add(choice.answers());
            choice.given().forEach(stands -> {
                named.add(stands.left());
                named.add(stands.right());
            });
            named.forEach(one -> bind(Map.of(operation, one), Function.identity(), null,
                    Question::isANumber, "an argument a case of the definition names"));
        }));
        return rules;
    }

    /** As {@link #bind}, for the arguments a bound names: the one the result is bounded against, and
     * the one a condition on the rule reads. Each is a separate claim about a separate argument. */
    private static Map<ValueName, List<ResultBound>> bindBounds(
            Map<ValueName, List<ResultBound>> rules) {
        rules.forEach((operation, bounds) -> bounds.forEach(bound -> {
            List<ArgumentRef> named = new ArrayList<>();
            if (bound.against() != null) {
                named.add(bound.against());
            }
            if (bound.provided() instanceof Provided.ConstantAboveZero constant) {
                named.add(constant.argument());
            }
            named.forEach(one -> bind(Map.of(operation, one), Function.identity(), null,
                    Question::isANumber, "an argument a bound on the result names"));
        }));
        return rules;
    }

    /** As {@link #bind}, for a rule that names more than one argument: each is held to the
     * declaration on its own, since each is a separate claim about a separate argument. */
    static Map<ValueName, List<ArgumentRef>> bindEach(Map<ValueName, List<ArgumentRef>> rules, ArgumentRef derived,
                                                Predicate<Type> required, String what) {
        rules.forEach((operation, reads) -> reads.forEach(one ->
                bind(Map.of(operation, one), Function.identity(), derived, required, what)));
        return rules;
    }

    /**
     * {@code rules}, once every row has been held to the operation it is about: the operation is one
     * the library declares, the argument it names is one that declaration has, and what stands there
     * is what the rule is about. A row naming a part of something the signature says the operation
     * does not hand is caught by {@link ArgumentRef}; one that writes a position the signature already
     * answers is caught here, since two answers to one question are what come apart later.
     */
    static <T> Map<ValueName, T> bind(Map<ValueName, T> rules, Function<T, ArgumentRef> reads,
                                      ArgumentRef derived, Predicate<Type> required, String what) {
        rules.forEach((operation, rule) -> {
            // Every row here is about an operation the library declares, so the key says which
            // library and which operation rather than a spelling this would have to take apart.
            if (!(operation instanceof ValueName.Stdlib library)) {
                throw new IllegalStateException("a rule about " + what + " is written for "
                        + operation + ", which is not a library operation");
            }
            Prelude.PreludeEntry entry = Prelude.entry(library.qualified());
            if (entry == null) {
                throw new IllegalStateException("a rule about " + what + " is written for "
                        + library.qualified() + ", which the library does not declare");
            }
            List<Type> params = entry.signature().params();
            ArgumentRef at = reads.apply(rule);
            int position = at.positionIn(operation);
            if (position < 0 || position >= params.size()) {
                throw new IllegalStateException(library.qualified() + " takes " + params.size()
                        + " argument(s), and the rule about " + what + " reads argument "
                        + (position + 1));
            }
            if (!required.test(params.get(position))) {
                throw new IllegalStateException("argument " + (position + 1) + " of "
                        + library.qualified() + " is not " + what);
            }
            if (at instanceof ArgumentRef.At && derived != null && Combinators.of(operation) != null
                    && derived.positionIn(operation) == position) {
                throw new IllegalStateException("the rule about " + what + " for "
                        + library.qualified()
                        + " writes the argument its signature already answers — say which part it is"
                        + " rather than where, so the two cannot come apart");
            }
        });
        return rules;
    }

    /** What {@link ElementLineage#derivesItsElementsFrom} answers with, read off the table here. */
    static ArgumentRef derivesItsElementsFrom(ValueName operation) {
        Built built = Bound.BUILDINGS.get(operation);
        if (built == null || built.outputs().size() != 1) {
            return null;
        }
        ElementLineage lineage = built.lineage();
        return (lineage instanceof ElementLineage.ClosureResult
                || lineage instanceof ElementLineage.InsideClosureResult)
                && lineage.source().elements() == 1 ? lineage.source().argument() : null;
    }

    /** What {@link ElementLineage#holdsTheElementsOf} answers with, read off the table here. */
    static ArgumentRef holdsTheElementsOf(ValueName operation) {
        Built built = Bound.BUILDINGS.get(operation);
        return built != null && built.outputs().size() == 1
                && built.lineage() instanceof ElementLineage.SameAs same
                && same.source().elements() == 1
                ? same.source().argument() : null;
    }

    /** The container {@code call} built its result from, or null where the check has no rule about
     * what the operation keeps. */
    static Source builtFrom(Core.PreservedCall call) {
        Built built = Bound.BUILDINGS.get(call.operation());
        return built == null ? null
                : new Source(built.from().of(call), built.shape(), built.size());
    }

    /**
     * The containers {@code e}'s result is no smaller than, in the order the rule names them.
     *
     * <p>{@code a ++ b} is here beside the table rather than in it. The library declares
     * {@code List.append} as {@code a ++ b}, so the two spellings are one operation and a rule about
     * one is a rule about the other; and a {@code String} has no {@code append} at all, so the
     * operator is the only spelling its concatenation has. A rule keyed by operation reaches neither,
     * both being written as an operator and not as a call.
     */
    static List<Core> noSmallerThan(Core e) {
        if (e instanceof Core.Binary b && b.op() == BinOp.CONCAT) {
            return List.of(b.left(), b.right());
        }
        if (!(e instanceof Core.PreservedCall call)) {
            return List.of();
        }
        List<ArgumentRef> reads = Bound.LOWER_BOUNDS.get(call.operation());
        if (reads == null) {
            return List.of();
        }
        List<Core> containers = new ArrayList<>(reads.size());
        for (ArgumentRef one : reads) {
            containers.add(one.of(call));
        }
        return containers;
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
        ArgumentRef reads = Bound.PROJECTIONS.get(call.operation());
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
    static BinOp operator(ValueName operation) {
        return OPERATOR_CALLS.get(operation);
    }

    /** Which argument a positive answer from {@code operation} names as the greater, or null where
     * its sign is not an order. */
    static PositiveOrder orderStatedBy(ValueName operation) {
        return ORDERS.get(operation);
    }

    /** Whether {@code operation} answers the order of its two arguments as a sign. */
    static boolean decidesOrder(ValueName operation) {
        return ORDERS.containsKey(operation);
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
            if (built != null && built.size() == Cardinality.SAME) {
                return sizeSource(built.container());
            }
        }
        return e;
    }

    private DischargeRules() {}
}
