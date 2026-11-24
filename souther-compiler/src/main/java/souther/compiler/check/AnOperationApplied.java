package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.OperationFact;
import souther.compiler.types.BinOp;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * An application of one of the language's operations, in any shape a tree gives one: the operation
 * standing as itself, a call to what its name reached, or the operator the library declares it as.
 *
 * <p>One reading of all of them. A reader that knew one shape answered for an operation in that
 * shape and said nothing — or something else — of the same operation in the other, and two readers
 * of one application that knew different shapes read it two ways. {@code a ++ b} is
 * {@code List.append(a, b)} over lists and {@code String.append(a, b)} over strings, so what either
 * operation says is said of the operator too.
 *
 * @param operation which operation is applied
 * @param args      what it is handed, in the order the declaration takes them
 */
public record AnOperationApplied(ValueName operation, List<Core> args) {

    /** {@code e} read as an application of an operation, or null where it applies none. */
    public static AnOperationApplied of(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.PreservedCall kept ->
                    asTheOperationItAgreesWith(kept) instanceof AnOperationApplied agreed
                    ? agreed : new AnOperationApplied(kept.declared().operation(), kept.args());
            case Core.Call call when call.fn() instanceof Core.Reached reached ->
                    new AnOperationApplied(reached.denotes(), call.args());
            // The checker types the operator over two strings or two lists and refuses it over
            // anything else, so a join that is no string's is a list's: the string's append and the
            // list's are the two operations it can be.
            case Core.Binary joined when joined.op() == BinOp.CONCAT
                    && DefaultBoundOperationFacts.get().operationFor(BinOp.CONCAT, joined.type())
                    instanceof ValueName operation ->
                    new AnOperationApplied(operation, List.of(joined.left(), joined.right()));
            case null, default -> null;
        };
    }

    /**
     * {@code call} as the application of the operation it agrees with where it is given the string
     * it is, with the arguments that remain; null where it is anything else. What is said of
     * either is said of both ({@link OperationFact.AgreesWithAnotherWhereItIsGivenText}).
     */
    static AnOperationApplied asTheOperationItAgreesWith(Core.PreservedCall call) {
        BoundOperationFact.AgreesWithAnotherWhereItIsGivenText agrees =
                DefaultBoundOperationFacts.get().agreesWhereItIsGivenText(call.operation());
        if (agrees == null || agrees.position() >= call.args().size()
                || !(Core.withoutStanding(call.args().get(agrees.position()))
                        instanceof Core.Str given)
                || !given.value().equals(agrees.text())) {
            return null;
        }
        List<Core> remaining = new ArrayList<>(call.args());
        remaining.remove(agrees.position());
        return new AnOperationApplied(agrees.other().operation(), remaining);
    }

    /** Whether it puts two lists end to end: the operation declared to be the operator
     *  {@code ++}, over a list. */
    public boolean putsListsEndToEnd() {
        return DefaultBoundOperationFacts.get().putsListsEndToEnd(operation);
    }

    /** The two arguments of a comparison that answers the order of them: the one a positive answer
     *  names as the greater, and the other. */
    public record Ordered(Core greater, Core lesser) {}

    /**
     * The two arguments it is handed, the greater first, where its answer is a sign that states
     * which of them is the greater and nought that they are equal — or null where it is no such
     * comparison ({@link BoundOperationFact.StatesTheOrderOfItsArguments}).
     *
     * <p>Which of the two a positive answer names is the operation's, and is not the same for all:
     * {@code compare(a, b)} is positive where {@code a} is the greater and
     * {@code daysBetween(a, b)} where {@code b} is. A reader that took the two as they were
     * handed would read the second one the wrong way round.
     */
    public Ordered ordersItsArguments() {
        BoundOperationFact.StatesTheOrderOfItsArguments order =
                DefaultBoundOperationFacts.get().statesTheOrderOfItsArguments(operation);
        Core greater = order == null ? null : argument(order.greater());
        Core lesser = order == null ? null : argument(order.lesser());
        return greater == null || lesser == null ? null : new Ordered(greater, lesser);
    }

    /** What an operation that answers a closure's answer on what an option holds is handed. */
    public record Mapped(Core option, Core closure) {}

    /**
     * What it is handed where it answers the closure's answer on what an option holds, and holds
     * a value exactly where the option does, or null where it does not — as the library declares
     * it ({@link BoundOperationFact.AnswersTheClosureOnWhatItHolds}).
     */
    public Mapped mapsAnOption() {
        BoundOperationFacts.ClosureOnWhatItHolds declared =
                DefaultBoundOperationFacts.get().answersTheClosureOnWhatItHolds(operation);
        Core option = declared == null ? null : argument(declared.option());
        Core closure = declared == null ? null : argument(declared.closure());
        return option == null || closure == null ? null : new Mapped(option, closure);
    }

    /**
     * What it asks whether it holds nothing of, where it is an emptiness check, or null where it
     * is not — as the library declares it ({@link BoundOperationFact.MeansTheSameAsASizeOfNought}).
     */
    public Core whoseEmptinessItAsks() {
        BoundOperationFact.MeansTheSameAsASizeOfNought declared =
                DefaultBoundOperationFacts.get().meansTheSameAsASizeOfNought(operation);
        return declared == null ? null : argument(declared.of());
    }

    /** What a lookup is handed: the key the value is looked up under and the container that files
     *  it. */
    public record Lookup(Core key, Core container) {}

    /**
     * What it is handed where it looks a value up under a key, or null where the operation is no
     * lookup — as the library declares it ({@link BoundOperationFact.AnswersTheValueFiledUnder}).
     */
    public Lookup lookup() {
        BoundOperationFacts.Lookup declared = DefaultBoundOperationFacts.get().looksUp(operation);
        Core key = declared == null ? null : argument(declared.key());
        Core container = declared == null ? null : argument(declared.container());
        return key == null || container == null ? null : new Lookup(key, container);
    }

    /**
     * What a search for a member is handed: what is looked for, the container it is looked for in,
     * and whether it is a key of a map that is looked for and not an element.
     */
    public record Searched(Core member, Core container, boolean aKey) {}

    /**
     * What it looks for and where, where it looks a value up under a key or asks whether a
     * container holds a member, or null where it does neither — as the library declares it
     * ({@link BoundOperationFact.AnswersTheValueFiledUnder},
     * {@link BoundOperationFact.AnswersWhetherItHolds}).
     */
    public Searched searches() {
        Lookup lookup = lookup();
        if (lookup != null) {
            return new Searched(lookup.key(), lookup.container(), true);
        }
        BoundOperationFacts.Membership declared =
                DefaultBoundOperationFacts.get().holdsAMember(operation);
        Core member = declared == null ? null : argument(declared.member());
        Core container = declared == null ? null : argument(declared.container());
        return member == null || container == null ? null
                : new Searched(member, container, declared.aKey());
    }

    /** Whether it answers whether a container holds a member, as against looking a value up. */
    public boolean asksWhetherItHolds() {
        return DefaultBoundOperationFacts.get().holdsAMember(operation) != null;
    }

    /**
     * The operator it computes, where the library declares it to answer what that operator does
     * to its arguments and the language writes it as an operator too — or null where it does not.
     */
    public BinOp theOperatorItComputes() {
        return DischargeRules.operator(operation);
    }

    /** What a run of whole numbers is handed: where it starts and where it ends. */
    public record Between(Core from, Core to) {}

    /**
     * What it is handed where it answers every whole number from one to another, or null where it
     * does not — as the library declares it ({@link BoundOperationFact.HoldsEachWholeNumberInTurn}).
     */
    public Between between() {
        BoundOperationFacts.Between declared =
                DefaultBoundOperationFacts.get().holdsEachWholeNumberInTurn(operation);
        Core from = declared == null ? null : argument(declared.from());
        Core to = declared == null ? null : argument(declared.to());
        return from == null || to == null ? null : new Between(from, to);
    }

    /**
     * The text whose code points it answers, each the number it is, or null where it answers no
     * such list — as the library declares it ({@link BoundOperationFact.ListsTheCodePointsOf}).
     */
    public Core whoseCodePointsItLists() {
        DeclaredArgument declared = DefaultBoundOperationFacts.get().codePointsListedOf(operation);
        return declared == null ? null : argument(declared);
    }

    /** What a pick is handed: the place an element is picked at and the list it is picked from. */
    public record Picked(Core index, Core list) {}

    /**
     * What it is handed where it picks the element of a list at a place, or null where it does
     * not — as the library declares it ({@link BoundOperationFact.AnswersTheElementAt}).
     */
    public Picked picks() {
        BoundOperationFacts.ElementAt declared =
                DefaultBoundOperationFacts.get().elementAt(operation);
        Core index = declared == null ? null : argument(declared.index());
        Core list = declared == null ? null : argument(declared.list());
        return index == null || list == null ? null : new Picked(index, list);
    }

    /** What a put under a key is handed: the key, the value filed under it, and the container it
     *  is filed in. */
    public record Put(Core key, Core value, Core into) {}

    /**
     * What it is handed where it files a value under a key in a container, or null where the
     * operation puts nothing under a key — as the library declares it
     * ({@link BoundOperationFact.PutsAValueIn}).
     */
    public Put put() {
        BoundOperationFact.PutsAValueIn declared =
                DefaultBoundOperationFacts.get().putsAValueIn(operation);
        if (declared == null || declared.under().isEmpty()) {
            return null;
        }
        Core key = argument(declared.under().get());
        Core value = argument(declared.value());
        Core into = argument(declared.into());
        return key == null || value == null || into == null ? null : new Put(key, value, into);
    }

    /** What it passes where {@code which} stands, or null where it passes nothing there. */
    public Core argument(DeclaredArgument which) {
        int at = CallArguments.positionOf(which, operation);
        return at < 0 || at >= args.size() ? null : args.get(at);
    }
}
