package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.ElementShape;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * What the language's own operations do to the properties the invariant-discharge check tracks
 * (spec §invariant-discharge-preservation), and what each guarantees of what it answers
 * (spec §invariant-discharge-guarantees).
 *
 * <p>What the operations are is not here. That is declared where nothing reads it
 * ({@link souther.compiler.semantics.OperationFacts}), held to the library once
 * ({@link OperationFactBinder}), and read from what that binding made
 * ({@link BoundOperationFacts}); what is here is this check's reading of it — the shape a rule is
 * read at a call, and what the check concludes from one. A fact about an operation held in a
 * procedure that reads it is a fact its second reader has to be given by that procedure, which is
 * the arrangement the declarations were moved out of.
 *
 * <p>Everything below asks the bound facts and interprets nothing of its own: which argument a fact
 * names is a position the binder settled, and the one step left — from a position to the expression
 * standing there in a call — is {@link CallArguments}'.
 */
final class DischargeRules {

    /** The operation {@code name} of the library module published as {@code alias}, as what a name
     * reaching it denotes. Written as the two values it is, so that a row here says which library it
     * is about without a reader splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return ValueName.Stdlib.operation(alias, name);
    }

    /** The facts about the language's operations, held to the library this compiler ships. */
    private static BoundOperationFacts facts() {
        return DefaultBoundOperationFacts.get();
    }

    /** The container {@code call} built its result from, and what the building kept of it. */
    record Source(Core container, ElementShape shape, SizeAgainstItsSource size) {}

    /** Where a predicate reads its container at a call, and how far its statement travels. */
    record Carrying(Core.PreservedCall stated, DeclaredArgument at, Set<ElementShape> through) {

        Core container() {
            return CallArguments.of(at, stated);
        }

        /** {@code call} — a call to the same operation — with the container it reads replaced. */
        Core.PreservedCall over(Core.PreservedCall call, Core container) {
            if (!call.operation().equals(stated.operation())) {
                throw new IllegalStateException("a rule read for " + stated.operation()
                        + " was asked to rewrite a call to " + call.operation());
            }
            return CallArguments.replacedIn(at, call, container);
        }
    }

    /** The projection a predicate at a call is stated over, as the block it answers with. */
    record Projection(Core.PreservedCall stated, DeclaredArgument at, Core.Block projection) {

        /** The call this was read for, stated over {@code value} instead. */
        Core.PreservedCall over(Core value) {
            return CallArguments.replacedIn(at, stated, value);
        }
    }

    /** Denial, which the analysis representation keeps as the call it is. */
    static final ValueName NOT = op("Bool", "not");

    /** The operations each table has a rule for. What is asked of them is {@link Question}'s to
     * settle; these are so it can hold a rule to being one an operation is asked for. */
    static Set<ValueName> builtOperations() {
        return facts().buildsItsResultFrom();
    }

    static Set<ValueName> carryingOperations() {
        return facts().readsItsContainer();
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
    static Set<String> constructionKinds(Stdlib stdlib) {
        Set<String> kinds = new LinkedHashSet<>();
        facts().buildsItsResultFrom().forEach(operation -> {
            BuiltFrom<DeclaredArgument> built = facts().buildsItsResultFrom(operation);
            Stdlib.Entry entry = operation instanceof ValueName.Stdlib.Operation library
                    ? stdlib.entry(library) : null;
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
        return facts().meansTheSameAsASizeOfNought();
    }

    static Set<ValueName> quantifiers() {
        return facts().statesItsPredicateOfEveryElement();
    }

    static Set<ValueName> projections() {
        return facts().isStatedOverAProjection();
    }

    static Set<ValueName> sizeCalls() {
        return NumericMeasures.calls();
    }

    static Set<ValueName> numericResultOperations() {
        return facts().computesANumber();
    }

    static Set<ValueName> orderings() {
        return facts().statesTheOrderOfItsArguments();
    }

    /**
     * The operations that answer, counted, some arithmetic over what they were given.
     *
     * <p>Two sources and one question. Most of them say so by declaring the form
     * ({@link BoundOperationFacts#answersAFormOfItsArguments}); a sum and a difference say it by
     * being the arithmetic they are. Declaring the form for those as well would be the same
     * statement twice, and leaving them out of the question altogether would be worse: the silence
     * beside it says there is nothing true here, and of {@code Int.add} that is false.
     *
     * <p>Which of them are is {@link #operator} and not a reading of its own. What that answers is
     * what a call to such an operation is read as where it stands ({@link Terms#asOperator}), so
     * asking it here is what makes the two the same statement — a second reading agreeing with it
     * today is a second reading to keep agreeing with it, and where they came apart this question
     * would want a silence written for an operation the grammar reads as a {@code +}.
     *
     * <p>A product is left out because it is a form only where an operand is written down: what
     * multiplies each is the other.
     */
    static Set<ValueName> formOperations() {
        Set<ValueName> answered = new LinkedHashSet<>(facts().answersAFormOfItsArguments());
        for (ValueName operation : facts().computesANumber()) {
            BinOp written = operator(operation);
            if (written == BinOp.ADD || written == BinOp.SUB) {
                answered.add(operation);
            }
        }
        return answered;
    }

    /** What {@code operation} answers, counted, in what its arguments are counted as — or null
     *  where it states no such form. */
    static LinearForm<DeclaredArgument> answersAFormOf(ValueName operation) {
        return facts().answersAFormOfItsArguments(operation);
    }

    /**
     * The declared forms, by name, for the test that holds each to a construction it discharges.
     *
     * <p>Every one of them, and not a subset this check can carry. What this check can do with a
     * form is settled by whether it can name the counts the form is written over, and that is the
     * requirement every declared form was held to where it was bound
     * ({@link TypeRequirement#COUNTED}, on the result and on every argument named) — so a form that
     * is bound is a form this carries, and a second reading of the carriers here would be the
     * binder's question asked again below the binding.
     *
     * <p>Over the declared forms and not over everything that answers the question. A sum and a
     * difference answer it by being the arithmetic they are, and what reads them is the grammar; a
     * program firing one would be firing the operator.
     */
    static Set<String> formNames() {
        Set<String> names = new LinkedHashSet<>();
        facts().answersAFormOfItsArguments().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    /** Those of them the building table has, by name, for the test that holds each to a construction
     * it discharges. */
    static Set<String> builtNames() {
        Set<String> names = new LinkedHashSet<>();
        builtOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> boundedOperations() {
        return facts().boundsOnTheResult();
    }

    static Set<ValueName> choosingOperations() {
        return facts().isDefinedByCases();
    }

    /** Those of them the choosing table has, by name, for the test that holds each case to a
     * program that reaches it. */
    static Set<String> choosingNames() {
        Set<String> names = new LinkedHashSet<>();
        choosingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> shiftingOperations() {
        return facts().shiftsBy();
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
    static BoundOperationFact.ShiftsBy shiftBy(Core e) {
        return e instanceof Core.PreservedCall call ? facts().shiftsBy(call.operation()) : null;
    }

    /** Whether {@code operation} counts what two values stand apart by — the other side of the row a
     * shift is written in, read off that row rather than listed again. A measure named in a second
     * place is a measure the day somebody adds a shift and updates one of them. */
    static boolean isAMeasure(ValueName operation) {
        for (ValueName shift : facts().shiftsBy()) {
            if (facts().shiftsBy(shift).measure().operation().equals(operation)) {
                return true;
            }
        }
        return false;
    }

    /** The cases {@code e} is defined in, or an empty list where it is not a call to an operation
     * that answers one of the values it was given. */
    static List<DefinitionCase<DeclaredArgument>> chosenBy(Core e) {
        return e instanceof Core.PreservedCall call ? facts().isDefinedByCases(call.operation())
                : List.of();
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
        for (ValueName operation : facts().boundsOnTheResult()) {
            facts().boundsOnTheResult(operation).forEach(bound -> rows.add(operation.toString()));
        }
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
    static List<ResultBound<DeclaredArgument>> boundsOn(Core.PreservedCall call,
                                                        Function<Core, BigDecimal> constant) {
        return boundsOn(call.operation(), CallArguments.readAs(call, constant));
    }

    /**
     * The same, for a reader holding the operation and not a call to it: the rows whose condition is
     * met by what {@code constants} can say about the arguments.
     *
     * <p>{@link ConstantArguments#none()} therefore leaves the rows an operation states whatever it
     * is given, which for an operation the language hands no number is every row it has — a bound
     * may only name an argument that is a number, which the binder holds, so there is no other kind
     * for such an operation to have.
     */
    static List<ResultBound<DeclaredArgument>> boundsOn(
            ValueName operation, ConstantArguments<DeclaredArgument> constants) {
        List<ResultBound<DeclaredArgument>> rows = facts().boundsOnTheResult(operation);
        List<ResultBound<DeclaredArgument>> holding = new ArrayList<>(rows.size());
        for (ResultBound<DeclaredArgument> row : rows) {
            if (constants.satisfy(row.provided())) {
                holding.add(row);
            }
        }
        return holding;
    }

    /**
     * Whether what {@code signature} answers is what the argument at {@code position} holds.
     *
     * <p>The one reading of the relation, for the two questions asked about it: which operations an
     * accumulation may be declared of at all, and whether the argument one names is the one that
     * fits. Read twice, the range and the holding would be free to disagree about a signature, and
     * a fact would be refused where it is written for not fitting a shape the range let it be
     * declared under.
     */
    static boolean resultIsElementOf(Stdlib.Signature signature, int position) {
        if (position < 0 || position >= signature.params().size()) {
            return false;
        }
        Type element = Type.elementOfAContainer(signature.params().get(position));
        return element != null && element.equals(signature.result());
    }

    /**
     * The container {@code call} built its result from, and where each element of what it answers
     * came from — the lineage itself, for a reader that has an answer per alternative.
     *
     * <p>Beside {@link #builtFrom} and not instead of it. The four words are what a reader asking
     * "does what I know survive this" wants, and they are a projection; a reader that can say
     * something different about each of the things an element may be wants what the projection was
     * read off. Null where the elements came from more than one place, as the projection is refused
     * there: without one container there is nothing to ask the question of.
     */
    static Kept keptFrom(Core.PreservedCall call) {
        BuiltFrom<DeclaredArgument> built = facts().buildsItsResultFrom(call.operation());
        if (built == null || built.outputs().size() != 1 || built.lineage().source() == null) {
            return null;
        }
        return new Kept(CallArguments.of(built.from(), call), built.lineage());
    }

    /** A construction's source container and the lineage of the elements it answers. */
    record Kept(Core container, ElementLineage<DeclaredArgument> lineage) {}

    /** The container {@code call} built its result from, or null where the check has no rule about
     * what the operation keeps. */
    static Source builtFrom(Core.PreservedCall call) {
        BuiltFrom<DeclaredArgument> built = facts().buildsItsResultFrom(call.operation());
        return built == null ? null
                : new Source(CallArguments.of(built.from(), call), built.shape(), built.size());
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
        List<DeclaredArgument> reads = facts().resultIsNoSmallerThan(call.operation());
        List<Core> containers = new ArrayList<>(reads.size());
        for (DeclaredArgument one : reads) {
            containers.add(CallArguments.of(one, call));
        }
        return containers;
    }

    /** Where {@code call} reads the container it states its predicate of, or null where it is not a
     * predicate this carries anywhere. */
    static Carrying carried(Core.PreservedCall call) {
        BoundOperationFact.ReadsItsContainer carried = facts().readsItsContainer(call.operation());
        return carried == null ? null : new Carrying(call, carried.container(), carried.through());
    }

    /** The projection {@code call}'s predicate is stated over, or null where it is stated over the
     * element itself — or where what stands in that argument is not a block this can read. */
    static Projection projectionOf(Core.PreservedCall call, Denotations at) {
        DeclaredArgument reads = facts().isStatedOverAProjection(call.operation());
        if (reads == null) {
            return null;
        }
        Core.Block projection = Terms.blockOf(CallArguments.of(reads, call), at);
        return projection == null ? null : new Projection(call, reads, projection);
    }

    /** Whether {@code operation} counts what it is given, which is the narrow question the size
     *  machinery asks: what a container holds, and what an emptiness check means. */
    static boolean isSize(ValueName operation) {
        return NumericMeasures.isMeasure(operation);
    }

    /**
     * Whether what {@code operation} answers is a number taken of the one value it was given.
     *
     * <p>The wider question, and the one a vocabulary asks. Whether the check has something to say
     * about a call is not whether the call is a size: {@code Time.hour(t)} answers a number of
     * {@code t} the way {@code String.length(s)} answers one of {@code s}, and what is declared of
     * each is declared under the same proposition. Spelled as "is it a size", the vocabulary was the
     * size machinery's own predicate read for a second purpose, and the first operation that
     * answered a number without counting anything was left out of it silently (#1027).
     */
    static boolean answersANumberTakenOfItsArgument(ValueName operation) {
        return facts().takenAs(operation) != null;
    }

    static boolean isQuantifier(ValueName operation) {
        return facts().statesItsPredicateOfEveryElement(operation);
    }

    /**
     * The rewrite an emptiness check stands for, or null where {@code operation} is not one.
     *
     * <p>Answered with both operations read against their declarations. A reader with this has
     * what it takes to write the second call where the first stands and nothing left to check: that
     * the two take the same argument, and that a size is what one compares against nought, was
     * settled where both declarations were in hand.
     */
    static BoundOperationFact.MeansTheSameAsASizeOfNought sizeMeantBy(ValueName operation) {
        return facts().meansTheSameAsASizeOfNought(operation);
    }

    /** What {@code operation} computes and where it answers it, or null where the table says
     * nothing of it. */
    static NumericResult<DeclaredArgument> numericResult(ValueName operation) {
        // An expression that calls nothing is asked this, and answering it is what says so.
        return facts().computesANumber(operation);
    }

    /** The operator {@code operation} is, where it answers one directly and the language writes it
     * as an operator too — else null. What a call to it is read as where it stands. */
    static BinOp operator(ValueName operation) {
        NumericResult<DeclaredArgument> result = numericResult(operation);
        return result != null
                && result.at() instanceof NumericResult.Answered.Directly
                && result.computes()
                        instanceof Arithmetic.TheOperator written
                ? written.op() : null;
    }

    /** Which argument a positive answer from {@code operation} names as the greater, and which as
     * the lesser — or null where its sign is not an order. */
    static BoundOperationFact.StatesTheOrderOfItsArguments orderStatedBy(ValueName operation) {
        return facts().statesTheOrderOfItsArguments(operation);
    }

    /** Whether {@code operation} answers the order of its two arguments as a sign. */
    static boolean decidesOrder(ValueName operation) {
        return orderStatedBy(operation) != null;
    }

    /** Whether the check has a rule about what a call answers, rather than only about how to render
     * it. */
    static boolean readsAsATerm(ValueName operation) {
        return answersANumberTakenOfItsArgument(operation) || builtOperations().contains(operation)
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
            if (built != null && built.size() == SizeAgainstItsSource.SAME) {
                return sizeSource(built.container());
            }
        }
        return e;
    }

    private DischargeRules() {}
}
