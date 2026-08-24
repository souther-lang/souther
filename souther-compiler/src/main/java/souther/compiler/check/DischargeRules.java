package souther.compiler.check;

import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.ElementShape;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.PositiveOrder;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.types.BinOp;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
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
 * <p>What the operations are is not here. That is declared where nothing reads it
 * ({@link OperationFacts}); what is here is this check's reading of it — the shape a rule is read
 * at a call, and what the check concludes from one. A fact about an operation held in a procedure
 * that reads it is a fact its second reader has to be given by that procedure, which is the
 * arrangement the declarations were moved out of.
 *
 * <p>What each declaration is held to is here too, since holding one reads the library's own
 * signatures and asks what this check makes of a type. Every declaration is walked before any call
 * is read ({@link OperationFactBinder}), so a fact nothing here looks up is one this has held all
 * the same.
 */
final class DischargeRules {

    /** The operation {@code name} of the library module published as {@code alias}, as what a name
     * reaching it denotes. Written as the two values it is, so that a row here says which library it
     * is about without a reader splitting a spelling to find out. */
    private static ValueName op(String alias, String name) {
        return new ValueName.Stdlib(alias, name);
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

    /** The container {@code call} built its result from, and what the building kept of it. */
    record Source(Core container, ElementShape shape, SizeAgainstItsSource size) {}



    /** Where a predicate reads its container at a call, and how far its statement travels. */
    record Carrying(Core.PreservedCall stated, ArgumentRef at, Set<ElementShape> through) {

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
    record Projection(Core.PreservedCall stated, ArgumentRef at, Core.Block projection) {

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
        return Bound.buildsItsResultFrom();
    }

    static Set<ValueName> carryingOperations() {
        return OperationFacts.readsItsContainer();
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
        Bound.buildsItsResultFrom().forEach(operation -> {
            BuiltFrom built = Bound.buildsItsResultFrom(operation);
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
        return Bound.meansTheSameAsASizeOfNought();
    }

    static Set<ValueName> quantifiers() {
        return Bound.statesItsPredicateOfEveryElement();
    }

    static Set<ValueName> projections() {
        return Bound.isStatedOverAProjection();
    }

    static Set<ValueName> sizeCalls() {
        return NumericMeasures.calls();
    }

    static Set<ValueName> numericResultOperations() {
        return Bound.computesANumber();
    }

    static Set<ValueName> orderings() {
        return Bound.statesTheOrder();
    }

    /**
     * The operations that answer, counted, some arithmetic over what they were given.
     *
     * <p>Two sources and one question. Most of them say so by declaring the form
     * ({@link OperationFacts#answersAFormOfItsArguments}); a sum and a difference say it by being
     * the arithmetic they are. Declaring the form for those as well would be the same statement
     * twice, and leaving them out of the question altogether would be worse: the silence beside it
     * says there is nothing true here, and of {@code Int.add} that is false.
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
        Set<ValueName> answered = new LinkedHashSet<>(Bound.answersAFormOfItsArguments());
        for (ValueName operation : Bound.computesANumber()) {
            BinOp written = operator(operation);
            if (written == BinOp.ADD || written == BinOp.SUB) {
                answered.add(operation);
            }
        }
        return answered;
    }

    /** What {@code operation} answers, counted, in what its arguments are counted as — or null
     *  where it states no such form. */
    static souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef> answersAFormOf(
            ValueName operation) {
        return Bound.answersAFormOfItsArguments(operation);
    }

    /**
     * Those of them this check can carry, by name.
     *
     * <p>Every declaration is about the operation and not about a reader, so the ones here are a
     * subset of what is declared: what an operation answers is stated over the counts of its
     * arguments, and this check's arithmetic is over the numbers a model wrote. A date counts days
     * and is no number, so {@code Date.daysBetween} states a form this reads and cannot carry — the
     * partition can, since a position's count is what it works in.
     *
     * <p>Derived from what this side relates and not written as a list. A list is a second copy of
     * a capability, wrong the day the capability changes; asked this way, the operations that arrive
     * are exactly the ones an author could write a discharging program for.
     */
    private static Set<ValueName> formOperationsThisCarries() {
        Set<ValueName> carried = new LinkedHashSet<>();
        // Over the declared forms and not over everything that answers the question. A sum and a
        // difference answer it by being the arithmetic they are, and what reads them is the
        // grammar; a program firing one would be firing the operator.
        for (ValueName operation : Bound.answersAFormOfItsArguments()) {
            if (everyPartIsANumber(operation)) {
                carried.add(operation);
            }
        }
        return carried;
    }

    /**
     * Whether the result and every argument the declared form names stand at a number this check
     * relates.
     *
     * <p>Both ends, because the fact is an equation between them: what the operation answers,
     * counted, and what it was given, counted. A form whose arguments this can carry and whose
     * result it cannot is a form it cannot carry.
     *
     * <p>Asked with {@link Question#isANumber} where the binding asks
     * {@link Question#countsToANumber}. That is the difference between what is true of the
     * operation and what this check can do with it — a date counts and is no number, so
     * {@code Date.daysBetween} is declared and is not carried here.
     *
     * <p>The library has the operation and the argument is one it takes, both of which
     * {@link OperationFactBinder} held before any of this was asked. What is left to decide is what
     * stands there.
     */
    private static boolean everyPartIsANumber(ValueName operation) {
        Prelude.Signature signature =
                Prelude.entry(((ValueName.Stdlib) operation).qualified()).signature();
        if (!Question.isANumber(signature.result())) {
            return false;
        }
        List<Type> params = signature.params();
        return answersAFormOf(operation).coefs().keySet().stream().allMatch(argument ->
                Question.isANumber(params.get(CallArguments.positionIn(argument, operation))));
    }

    /** Those of them the read-through table has, by name, for the test that holds each to a
     * construction it discharges. */
    static Set<String> formNames() {
        Set<String> names = new LinkedHashSet<>();
        formOperationsThisCarries().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> boundedOperations() {
        return Bound.boundsOnTheResult();
    }

    static Set<ValueName> choosingOperations() {
        return Bound.isDefinedByCases();
    }

    /** Those of them the choosing table has, by name, for the test that holds each case to a
     * program that reaches it. */
    static Set<String> choosingNames() {
        Set<String> names = new LinkedHashSet<>();
        choosingOperations().forEach(operation -> names.add(operation.toString()));
        return names;
    }

    static Set<ValueName> shiftingOperations() {
        return Bound.shiftsBy();
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
    static OperationFact.ShiftsBy shiftBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.shiftsBy(call.operation()) : null;
    }

    /** Whether {@code operation} counts what two values stand apart by — the other side of the row a
     * shift is written in, read off that row rather than listed again. A measure named in a second
     * place is a measure the day somebody adds a shift and updates one of them. */
    static boolean isAMeasure(ValueName operation) {
        return Bound.measures().contains(operation);
    }

    /** The cases {@code e} is defined in, or null where it is not a call to an operation that
     * answers one of the values it was given. */
    static List<OperationFact.Case> chosenBy(Core e) {
        return e instanceof Core.PreservedCall call ? Bound.isDefinedByCases(call.operation())
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
        for (ValueName operation : Bound.boundsOnTheResult()) {
            Bound.boundsOnTheResult(operation).forEach(bound -> rows.add(operation.toString()));
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
    static List<ResultBound> boundsOn(Core.PreservedCall call,
                                      Function<Core, BigDecimal> constant) {
        List<ResultBound> rows =
                Bound.boundsOnTheResult(call.operation());
        List<ResultBound> holding = new ArrayList<>(rows.size());
        for (ResultBound row : rows) {
            if (CallArguments.holds(row.provided(), call, constant)) {
                holding.add(row);
            }
        }
        return holding;
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

        private static Set<ValueName> buildsItsResultFrom() {
            return OperationFacts.buildsItsResultFrom();
        }

        private static BuiltFrom buildsItsResultFrom(ValueName operation) {
            return OperationFacts.buildsItsResultFrom(operation);
        }
        private static OperationFact.ReadsItsContainer readsItsContainer(
                ValueName operation) {
            return OperationFacts.readsItsContainer(operation);
        }

        private static ArgumentRef isStatedOverAProjection(ValueName operation) {
            return OperationFacts.isStatedOverAProjection(operation);
        }

        private static Set<ValueName> isStatedOverAProjection() {
            return OperationFacts.isStatedOverAProjection();
        }

        private static List<ArgumentRef> resultIsNoSmallerThan(ValueName operation) {
            return OperationFacts.resultIsNoSmallerThan(operation);
        }

        private static boolean statesItsPredicateOfEveryElement(ValueName operation) {
            return OperationFacts
                    .statesItsPredicateOfEveryElement(operation);
        }

        private static Set<ValueName> statesItsPredicateOfEveryElement() {
            return OperationFacts.statesItsPredicateOfEveryElement();
        }

        private static ValueName meansTheSameAsASizeOfNought(ValueName operation) {
            return OperationFacts
                    .meansTheSameAsASizeOfNought(operation);
        }

        private static Set<ValueName> meansTheSameAsASizeOfNought() {
            return OperationFacts.meansTheSameAsASizeOfNought();
        }
        /** What the declarations came to, held to the library. The list is walked whole, so a fact
         *  nothing here looks up is one this has held all the same. */
        private static final List<OperationFacts.Declared> SEMANTICS =
                OperationFactBinder.bindAll();

        /**
         * What the language declares an operation answers.
         *
         * <p>Here rather than at the call site so that asking runs the binding above, which is what
         * the rest of this holder does for the tables beside it. The answer itself is the
         * declaration's; what asking through here adds is that it has been held to the library
         * first.
         */
        private static souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef>
                answersAFormOfItsArguments(ValueName operation) {
            return OperationFacts.answersAFormOfItsArguments(operation);
        }

        /** The operations declared to answer a form of their arguments, for the checks that hold
         *  each of them to firing. */
        private static Set<ValueName> answersAFormOfItsArguments() {
            return OperationFacts.answersAFormOfItsArguments();
        }

        private static Set<ValueName> statesTheOrder() {
            return OperationFacts.statesTheOrderOfItsArguments();
        }

        private static PositiveOrder statesTheOrder(
                ValueName operation) {
            return OperationFacts
                    .statesTheOrderOfItsArguments(operation);
        }

        private static Set<ValueName> shiftsBy() {
            return OperationFacts.shiftsBy();
        }

        private static OperationFact.ShiftsBy shiftsBy(
                ValueName operation) {
            return OperationFacts.shiftsBy(operation);
        }

        /** The measures the shifts are stated through, read off those rather than listed again. A
         *  measure named in a second place is a measure the day somebody adds a shift and updates
         *  one of them. */
        private static Set<ValueName> measures() {
            Set<ValueName> out = new LinkedHashSet<>();
            shiftsBy().forEach(operation -> out.add(shiftsBy(operation).measure()));
            return out;
        }

        private static Set<ValueName> boundsOnTheResult() {
            return OperationFacts.boundsOnTheResult();
        }

        private static List<ResultBound> boundsOnTheResult(
                ValueName operation) {
            return OperationFacts.boundsOnTheResult(operation);
        }
        private static Set<ValueName> isDefinedByCases() {
            return OperationFacts.isDefinedByCases();
        }

        private static List<OperationFact.Case> isDefinedByCases(
                ValueName operation) {
            return OperationFacts.isDefinedByCases(operation);
        }

        private static Set<ValueName> computesANumber() {
            return OperationFacts.computesANumber();
        }

        private static NumericResult computesANumber(
                ValueName operation) {
            return OperationFacts.computesANumber(operation);
        }
    }

    /**
     * As {@link #bind}, for the arithmetic an operation computes: it takes as many arguments as the
     * row hands over, and it answers its number where the row says it does.
     *
     * <p>The result position is the half a signature can disagree with silently. A row saying the
     * number arrives in the case carrying {@code Int} is read at an arm, and an arm that never
     * matches is an arm that reports nothing — so a union that gained a case, or lost the one the
     * row names, would leave the operation with a meaning no program reaches and no diagnostic
     * anywhere. Held here, before any call is read.
     */
    static void holdNumericResult(ValueName operation, NumericResult rule) {
        Prelude.Signature signature = holdTheOperationToTheLibrary(operation).signature();
        Type answers = Question.numberAnsweredBy(signature.result());
        List<Arithmetic.Reads> reads = rule.computes().reads();
        if (signature.params().size() != reads.size()) {
            throw new IllegalStateException(operation + " takes " + signature.params().size()
                    + " argument(s), and the arithmetic written for it reads " + reads.size());
        }
        for (int i = 0; i < reads.size(); i++) {
            if (!reads.get(i).heldBy(signature.params().get(i), answers)) {
                throw new IllegalStateException("argument " + (i + 1) + " of " + operation
                        + " is " + Type.show(signature.params().get(i))
                        + ", which the arithmetic written for it reads as " + reads.get(i));
            }
        }
        switch (rule.at()) {
            case NumericResult.Answered.Directly ignored ->
                    holdTheResultToTheDeclaration(operation, Question::isANumber,
                            "a number for the arithmetic it computes to be answered at");
            case NumericResult.Answered.InTheCaseCarrying(Type carried) -> {
                if (!(signature.result() instanceof Type.Union(Set<TypeSymbol> members))) {
                    throw new IllegalStateException(operation + " answers "
                            + Type.show(signature.result())
                            + ", which has no case for the number it computes to arrive in");
                }
                if (!carried.equals(answers)) {
                    throw new IllegalStateException(operation + " answers no case carrying "
                            + Type.show(carried));
                }
                if (rule.unless() == null) {
                    throw new IllegalStateException(operation + " answers its number as one case"
                            + " of a union, so when the other case comes back is what that case"
                            + " means and is not written down");
                }
                // The condition names no case, so it says what every case that is not the
                // number's says — which is one statement only where there is one such case. A
                // union that gained a third would have an arm establishing a condition it was
                // not taken under, which is a wrong fact rather than a missing one, and nothing
                // downstream could tell: an arm is read the same way whichever case it names.
                // Where a second failure is wanted, the condition is what has to name its case.
                if (members.size() != 2) {
                    throw new IllegalStateException(operation + " answers "
                            + members.size() + " cases, and when it answers no number is"
                            + " written as one condition — which says what one other case"
                            + " means and cannot say what several do");
                }
            }
        }
        if (rule.unless() != null) {
            holdToTheDeclaration(operation, rule.unless().argument(), null,
                    Question::isANumber, "the argument a failure is decided by");
        }
    }

    /**
     * As {@link #bind}, for a rule stating a shift through a measure: the amount is a number, the
     * value shifted is of the type the measure counts, and the measure counts two of what the
     * operation answers. A rule pairing an operation with a measure of something else would state a
     * relation between two values that have none.
     */
    static void holdShift(ValueName operation, OperationFact.ShiftsBy
            shift) {
        holdToTheDeclaration(operation, shift.amount(), null, Question::isANumber,
                "the amount a shift moves by");
        Prelude.PreludeEntry counts = Prelude.entry(shift.measure().qualified());
        if (counts == null) {
            throw new IllegalStateException("the rule about " + operation + " counts through "
                    + shift.measure().qualified() + ", which the library does not declare");
        }
        Prelude.PreludeEntry shifted = holdTheOperationToTheLibrary(operation);
        List<Type> counted = counts.signature().params();
        if (counted.size() != 2 || !Question.isANumber(counts.signature().result())
                || !counted.get(0).equals(shifted.signature().result())
                || !counted.get(1).equals(shifted.signature().result())) {
            throw new IllegalStateException(shift.measure().qualified()
                    + " does not count two of what " + operation + " answers apart as a number");
        }
        holdToTheDeclaration(operation, shift.of(), null,
                t -> t.equals(shifted.signature().result()), "the value a shift moves from");
    }

    /** As {@link #bind}, for the arguments a case names: the one it answers, and the two sides of
     * each condition it is reached under. */
    static void holdCase(ValueName operation, OperationFact.Case one) {
        holdTheResultToTheDeclaration(operation, Question::isANumber,
                "a number for a case of the definition to answer");
        List<ArgumentRef> named = new ArrayList<>();
        named.add(one.answers());
        one.given().forEach(stands -> {
            named.add(stands.left());
            named.add(stands.right());
        });
        named.forEach(each -> holdToTheDeclaration(operation, each, null, Question::isANumber,
                "an argument a case of the definition names"));
    }

    /** As {@link #bind}, for the arguments a bound names: the one the result is bounded against, and
     * the one a condition on the rule reads. Each is a separate claim about a separate argument. */
    static void holdBound(ValueName operation, ResultBound bound) {
        holdTheResultToTheDeclaration(operation, Question::isANumber,
                "a number for a bound on the result to hold of");
        List<ArgumentRef> named = new ArrayList<>();
        if (bound.against() != null) {
            named.add(bound.against());
        }
        if (bound.provided()
                instanceof ResultBound.Provided.ConstantAboveZero
                constant) {
            named.add(constant.argument());
        }
        named.forEach(one -> holdToTheDeclaration(operation, one, null, Question::isANumber,
                "an argument a bound on the result names"));
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
        rules.forEach((operation, rule) ->
                holdToTheDeclaration(operation, reads.apply(rule), derived, required, what));
        return rules;
    }

    /**
     * The library's declaration of {@code operation}, or a build that does not start.
     *
     * <p>What every fact owes, whatever else it says. A fact is a proposition about an operation,
     * so an operation the library does not have is a fact about nothing — and that is true of a
     * fact naming no argument as much as of one that names three.
     *
     * <p>Its own step rather than the first half of {@link #holdToTheDeclaration}, because there it
     * was reached only by a fact that had an argument to check. A fact naming none went through an
     * arm with nothing in it and was never held to anything, so which declarations were bound
     * depended on which kinds of fact happened to name an argument. A kind added later would have
     * lost the same way, silently, on the day its arm was written empty.
     */
    static Prelude.PreludeEntry holdTheOperationToTheLibrary(ValueName operation) {
        // Every fact is about an operation the library declares, so the operation says which
        // library and which name rather than a spelling this would have to take apart.
        if (!(operation instanceof ValueName.Stdlib library)) {
            throw new IllegalStateException("a fact is declared of " + operation
                    + ", which is not a library operation");
        }
        Prelude.PreludeEntry entry = Prelude.entry(library.qualified());
        if (entry == null) {
            throw new IllegalStateException("a fact is declared of " + library.qualified()
                    + ", which the library does not declare");
        }
        return entry;
    }

    /**
     * The library's declaration of {@code operation}, once what it answers is what a fact about its
     * result is about.
     *
     * <p>Beside {@link #holdToTheDeclaration} and for the half it cannot reach. That one names an
     * argument, so a fact whose proposition mentions the result had nothing to say it with, and
     * each kind that needed the result said it its own way or not at all: {@code BoundsItsResult}
     * and {@code IsDefinedByCases} are stated of a number and were held only of their arguments.
     * Improvising a check per kind defaults to omitting it, which is how a fact naming no argument
     * once went through an empty arm ({@link #holdTheOperationToTheLibrary}).
     *
     * <p>What is required is the caller's, since what a fact says of the result is the fact's. A
     * form is about a count and a bound about a number, and the difference between those two is a
     * difference between the propositions and not between two ways of holding one.
     */
    static void holdTheResultToTheDeclaration(ValueName operation, Predicate<Type> required,
            String what) {
        Type result = holdTheOperationToTheLibrary(operation).signature().result();
        if (result == null || !required.test(result)) {
            throw new IllegalStateException("what " + ((ValueName.Stdlib) operation).qualified()
                    + " answers is " + (result == null ? "left to its body" : Type.show(result))
                    + ", which is not " + what);
        }
    }

    /**
     * Holds a declared form to the library: what it answers counts, and so does every argument it
     * is written over.
     *
     * <p>Both ends, because the fact is an equation between them —
     * {@code count(result) = Σ cᵢ·count(argᵢ) + k}. Held of the arguments alone it was half a
     * statement: {@code List.take(n, xs)} declared to answer the number of its first argument
     * passed, that argument being an {@code Int}, while what it answers is a list and has no count
     * for the equation to be about.
     *
     * <p>Counted rather than a number, because that is what the fact says. A date is no number and
     * counts days; whether this check can then do anything with such a form is a different question
     * and belongs to the check ({@link #formOperationsThisCarries}).
     */
    static void holdAFormOfItsArguments(ValueName operation,
            souther.compiler.numeric.NumericDomain.LinearForm<ArgumentRef> form) {
        holdTheResultToTheDeclaration(operation, Question::countsToANumber,
                "a value with a count for a form of its arguments to be about");
        for (ArgumentRef argument : form.coefs().keySet()) {
            holdToTheDeclaration(operation, argument, null, Question::countsToANumber,
                    "an argument the result is a form of");
        }
    }

    /** The same, for one rule. Asked per rule so that whatever holds a whole declaration source can
     *  walk it and hold each of them, rather than reaching for a table of its own. */
    static void holdToTheDeclaration(ValueName operation, ArgumentRef at, ArgumentRef derived,
                                     Predicate<Type> required, String what) {
        Prelude.PreludeEntry entry = holdTheOperationToTheLibrary(operation);
        ValueName.Stdlib library = (ValueName.Stdlib) operation;
        List<Type> params = entry.signature().params();
        int position = CallArguments.positionIn(at, operation);
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
                && CallArguments.positionIn(derived, operation) == position) {
            throw new IllegalStateException("the rule about " + what + " for "
                    + library.qualified()
                    + " writes the argument its signature already answers — say which part it is"
                    + " rather than where, so the two cannot come apart");
        }
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
        BuiltFrom built = Bound.buildsItsResultFrom(call.operation());
        if (built == null || built.outputs().size() != 1 || built.lineage().source() == null) {
            return null;
        }
        return new Kept(CallArguments.of(built.from(), call), built.lineage());
    }

    /** A construction's source container and the lineage of the elements it answers. */
    record Kept(Core container, ElementLineage lineage) {}

    /** The container {@code call} built its result from, or null where the check has no rule about
     * what the operation keeps. */
    static Source builtFrom(Core.PreservedCall call) {
        BuiltFrom built = Bound.buildsItsResultFrom(call.operation());
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
        List<ArgumentRef> reads = Bound.resultIsNoSmallerThan(call.operation());
        if (reads == null) {
            return List.of();
        }
        List<Core> containers = new ArrayList<>(reads.size());
        for (ArgumentRef one : reads) {
            containers.add(CallArguments.of(one, call));
        }
        return containers;
    }

    /** Where {@code call} reads the container it states its predicate of, or null where it is not a
     * predicate this carries anywhere. */
    static Carrying carried(Core.PreservedCall call) {
        OperationFact.ReadsItsContainer carried =
                Bound.readsItsContainer(call.operation());
        return carried == null ? null : new Carrying(call, carried.container(), carried.through());
    }

    /** The projection {@code call}'s predicate is stated over, or null where it is stated over the
     * element itself — or where what stands in that argument is not a block this can read. */
    static Projection projectionOf(Core.PreservedCall call, Denotations at) {
        ArgumentRef reads = Bound.isStatedOverAProjection(call.operation());
        if (reads == null) {
            return null;
        }
        Core.Block projection = Terms.blockOf(CallArguments.of(reads, call), at);
        return projection == null ? null : new Projection(call, reads, projection);
    }

    static boolean isSize(ValueName operation) {
        return NumericMeasures.isMeasure(operation);
    }

    static boolean isQuantifier(ValueName operation) {
        return Bound.statesItsPredicateOfEveryElement(operation);
    }

    /** The size call an emptiness check means, or null where {@code operation} is not one. */
    static ValueName sizeMeantBy(ValueName operation) {
        return Bound.meansTheSameAsASizeOfNought(operation);
    }

    /** What {@code operation} computes and where it answers it, or null where the table says
     * nothing of it. */
    static NumericResult numericResult(ValueName operation) {
        // An expression that calls nothing is asked this, and answering it is what says so. The
        // tables are immutable maps, which refuse a null key rather than answering for it, and a
        // reader that guarded the call itself would be one guard per reader.
        return Bound.computesANumber(operation);
    }

    /** The operator {@code operation} is, where it answers one directly and the language writes it
     * as an operator too — else null. What a call to it is read as where it stands. */
    static BinOp operator(ValueName operation) {
        NumericResult result = numericResult(operation);
        return result != null
                && result.at() instanceof NumericResult.Answered.Directly
                && result.computes()
                        instanceof Arithmetic.TheOperator written
                ? written.op() : null;
    }

    /** Which argument a positive answer from {@code operation} names as the greater, or null where
     * its sign is not an order. */
    static PositiveOrder orderStatedBy(ValueName operation) {
        return Bound.statesTheOrder(operation);
    }

    /** Whether {@code operation} answers the order of its two arguments as a sign. */
    static boolean decidesOrder(ValueName operation) {
        return orderStatedBy(operation) != null;
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
            if (built != null && built.size() == SizeAgainstItsSource.SAME) {
                return sizeSource(built.container());
            }
        }
        return e;
    }

    private DischargeRules() {}
}
