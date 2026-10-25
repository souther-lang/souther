package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A rule saying the elements of a list that stand at one case of a field add up to what those at
 * another case of it do.
 *
 * <p>Read where two totals are compared for equality and each is a walk over the same list adding
 * one number of an element when a field of the element is one case, and leaving the total as it was
 * otherwise. Two such totals over the same list and the same number, at two cases, are the sides of
 * the rule; what else they might be made of is left unread, since a builder told only that the
 * sides balance would build lists the rule refuses.
 *
 * <p>A fact about the list as a whole, which is what makes it a rule of the value holding the list:
 * the elements may be any, and which of them the rule asks for depends on how many stand at each
 * case.
 */
public final class SidesBalanced {

    private static final ValueName.Stdlib.Operation COMPARE =
            ValueName.Stdlib.operation("Decimal", "compare");
    private static final ValueName.Stdlib.Operation FOLD =
            ValueName.Stdlib.operation("List", "foldFrom");
    private static final ValueName.Stdlib.Operation ADD =
            ValueName.Stdlib.operation("Decimal", "add");

    private SidesBalanced() {}

    /**
     * What a rule asks of a list, as the expression it names the list with.
     *
     * @param list     what the list is written as
     * @param field    the field of an element that tells which side it is on
     * @param number   the fields of an element that lead to the number it adds
     * @param one      the case one side stands at
     * @param other    the case the other side stands at
     */
    public record Stated(Core list, String field, List<String> number, TypeSymbol one,
                         TypeSymbol other) {}

    /** What a rule asks of the list at a place, without the expression it was written with. */
    public record Requirement(String field, List<String> number, TypeSymbol one,
                              TypeSymbol other) {

        public Requirement {
            number = List.copyOf(number);
        }
    }

    /** One side: the list, and what it adds of an element at which case. */
    private record Side(Core list, String field, List<String> number, TypeSymbol at) {}

    /**
     * {@code clause} read as two totals of one list being equal, or null where it states nothing of
     * the kind.
     */
    public static Stated read(Core clause) {
        Core here = Core.withoutStanding(clause);
        if (!(here instanceof Core.Binary same) || same.op() != BinOp.EQ) {
            return null;
        }
        Core left = Core.withoutStanding(same.left());
        Core right = Core.withoutStanding(same.right());
        // The totals compared as decimals are compared by their order, and an answer of nought is
        // their equality.
        if (AnOperationApplied.of(left) instanceof AnOperationApplied(var operation, var args)
                && operation.equals(COMPARE) && args.size() == 2
                && right instanceof Core.Int nought && nought.value() == 0) {
            return sides(args.get(0), args.get(1));
        }
        return sides(left, right);
    }

    private static Stated sides(Core first, Core second) {
        Side one = side(first, new HashMap<>());
        Side other = side(second, new HashMap<>());
        if (one == null || other == null || one.at().equals(other.at())
                || !one.field().equals(other.field()) || !one.number().equals(other.number())
                || !sameList(one.list(), other.list())) {
            return null;
        }
        return new Stated(one.list(), one.field(), one.number(), one.at(), other.at());
    }

    private static boolean sameList(Core one, Core other) {
        return Core.withoutStanding(one) instanceof Core.Read first
                && Core.withoutStanding(other) instanceof Core.Read second
                && first.binding().equals(second.binding());
    }

    /** A total of a list, adding one number of an element where a field of it is a case. */
    private static Side side(Core e, Map<BindingId, Core> given) {
        Core walk = LetBound.resolved(e, given);
        if (!(AnOperationApplied.of(walk) instanceof AnOperationApplied(var operation, var args))
                || !operation.equals(FOLD) || args.size() != 4
                || !(LetBound.resolved(args.get(0), given) instanceof Core.Block step)
                || step.params().size() != 2
                || !(LetBound.resolved(args.get(1), given) instanceof Core.Decimal seed)
                || seed.value().signum() != 0
                || !(LetBound.resolved(args.get(2), given) instanceof Core.Read list)) {
            return null;
        }
        BindingId total = step.params().get(0).binding();
        BindingId element = step.params().get(1).binding();
        if (!(Core.withoutStanding(step.body()) instanceof Core.If choice)
                || !(Core.withoutStanding(choice.els()) instanceof Core.Read kept)
                || !kept.binding().equals(total)
                || !(Core.withoutStanding(choice.cond()) instanceof Core.Binary at)
                || at.op() != BinOp.EQ) {
            return null;
        }
        // Which field of the element the condition reads, and which case it is compared with.
        List<String> field = stepsFrom(at.left(), element);
        Core named = at.right();
        if (field == null) {
            field = stepsFrom(at.right(), element);
            named = at.left();
        }
        if (field == null || field.size() != 1
                || !(LetBound.resolved(named, given) instanceof Core.UnitValue unit)) {
            return null;
        }
        // The number added to the total, in either order.
        if (!(AnOperationApplied.of(Core.withoutStanding(choice.then()))
                instanceof AnOperationApplied(var added, var parts))
                || !added.equals(ADD) || parts.size() != 2) {
            return null;
        }
        List<String> number = isTheTotal(parts.get(0), total) ? stepsFrom(parts.get(1), element)
                : isTheTotal(parts.get(1), total) ? stepsFrom(parts.get(0), element) : null;
        if (number == null || number.isEmpty()) {
            return null;
        }
        return new Side(list, field.getFirst(), number, unit.data());
    }

    private static boolean isTheTotal(Core e, BindingId total) {
        return Core.withoutStanding(e) instanceof Core.Read read && read.binding().equals(total);
    }

    /** The fields read off the element {@code element} to make {@code e}, or null where it is
     *  anything else. */
    private static List<String> stepsFrom(Core e, BindingId element) {
        List<String> steps = new ArrayList<>();
        Core at = Core.withoutStanding(e);
        while (at instanceof Core.FieldAccess access) {
            steps.addFirst(access.field());
            at = Core.withoutStanding(access.target());
        }
        return at instanceof Core.Read read && read.binding().equals(element) ? steps : null;
    }

    /**
     * What the rules written on {@code named} ask of the list at each place, by the place.
     *
     * <p>Read off what each rule states ({@link InvariantStatements}), so a rule stated through a
     * helper is the rule written out. A rule whose list is not a field of the declaration is left
     * out: nothing builds for a rule it cannot name the place of.
     */
    public static Map<RuleKey, List<Requirement>> writtenOn(TypeSymbol.AtModule named,
                                                            RuleReadingSource source) {
        RecordRules rules = RecordRules.of(named, source);
        if (rules == null) {
            return Map.of();
        }
        Map<RuleKey, List<Requirement>> out = new LinkedHashMap<>();
        for (InvariantStatement one : rules.statements()) {
            if (!(one instanceof InvariantStatement.BalancesSides it)) {
                continue;
            }
            RuleKey where = rules.fieldAt(it.balanced().list());
            if (where != null) {
                out.computeIfAbsent(where, _ -> new ArrayList<>())
                        .add(new Requirement(it.balanced().field(), it.balanced().number(),
                                it.balanced().one(), it.balanced().other()));
            }
        }
        Map<RuleKey, List<Requirement>> held = new LinkedHashMap<>();
        out.forEach((where, requirements) -> {
            if (buildable(where, requirements) && elementsStandAlone(named, where, source)) {
                held.put(where, List.copyOf(requirements));
            }
        });
        return Map.copyOf(held);
    }

    /**
     * Whether the elements of the list at {@code list} are records with no rule of their own.
     *
     * <p>The numbers are chosen among those the number's type admits, and the case is chosen
     * beside them. A rule of the element that reads its case and its number together
     * ({@code side == Credit || amount >= 10}) makes the numbers a case admits depend on the case,
     * and one that reads either with a third field makes them depend on that, so an element with
     * any rule of its own is one whose numbers cannot be chosen apart from its fields. Which fields
     * a rule reads is not asked: a rule stated through a helper is read through the helper only as
     * far as the statements go, and the answer worth having is that nothing relates them.
     */
    private static boolean elementsStandAlone(TypeSymbol.AtModule named, RuleKey list,
                                              RuleReadingSource source) {
        if (!(TypeView.shapeOf(Type.ref(named), source.inners(), source.symbols(), source.kinds(),
                source.sums()) instanceof Shape.Product(TypeSymbol _, var fields))
                || !(fields.get(list.steps().getFirst()) instanceof Type listType)) {
            return false;
        }
        TypeView view = TypeView.of(listType, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (!(view.shape() instanceof Shape.Sequence(Shape.Sequence.Kind kind, Type element))
                || kind != Shape.Sequence.Kind.LIST) {
            return false;
        }
        TypeView elementView = TypeView.of(element, source.inners(), source.symbols(),
                source.kinds(), source.sums());
        if (!(elementView.shape() instanceof Shape.Product product)
                || !(product.name() instanceof TypeSymbol.AtModule record)
                || elementView.wrappers().stream().anyMatch(each -> !each.equals(record))) {
            return false;
        }
        RecordRules rules = RecordRules.of(record, source);
        return rules != null && rules.declaresNothing();
    }

    /**
     * Whether a list can be built whose sides balance as {@code requirements} ask of it.
     *
     * <p>The one answer to what the builders of a record can keep, which is what a rule must be
     * for a reading to call it read. The list is a field of the record, the number an element adds
     * is one of its fields or a name's value, and the list is asked to balance one pair of sides:
     * two pairs are two equations over the same elements, and nothing here solves them together.
     */
    private static boolean buildable(RuleKey list, List<Requirement> requirements) {
        if (list.steps().size() != 1 || requirements.size() != 1) {
            return false;
        }
        List<String> number = requirements.getFirst().number();
        return number.size() == 1 || (number.size() == 2 && number.get(1).equals("value"));
    }
}
