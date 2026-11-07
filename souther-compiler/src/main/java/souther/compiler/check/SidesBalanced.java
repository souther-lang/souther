package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.PieceOfAnElement;
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
 * <p>Read where two totals are held equal and each is a walk over the same list adding one number of
 * an element when a field of the element is one case, and leaving the total as it was otherwise —
 * or a walk adding it of every element a filter kept by that case. Two such totals over the same
 * list and the same number, at two cases, are the sides of
 * the rule; what else they might be made of is left unread, since a builder told only that the
 * sides balance would build lists the rule refuses.
 *
 * <p>A fact about the list as a whole, which is what makes it a rule of the value holding the list:
 * the elements may be any, and which of them the rule asks for depends on how many stand at each
 * case.
 */
public final class SidesBalanced {

    private static final ValueName.Stdlib.Operation FOLD =
            ValueName.Stdlib.operation("List", "foldFrom");

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

    /**
     * One side: the list, and what it adds of an element at which case. A value, so that two totals
     * written twice over one list are one side and cancel.
     */
    private record Side(BindingId list, String field, List<String> number, TypeSymbol at) {

        Side {
            number = List.copyOf(number);
        }
    }

    /** A field of an element and the case it is held equal to. */
    private record AtACase(String field, TypeSymbol at) {}

    /**
     * {@code leaf}, a part of a clause standing under {@code positive}, read as two totals of one
     * list being equal, or null where it states nothing of the kind.
     */
    public static Stated read(Core leaf, boolean positive) {
        StatedComparison stated = Core.withoutStanding(leaf) instanceof Core.Binary bin
                ? StatedComparison.of(bin, positive) : null;
        return stated == null ? null : read(stated);
    }

    /**
     * What {@code stated} says of two totals, or null where it states nothing of the kind.
     *
     * <p>As the comparison it is, with its denial spent, and its sides read as the library says
     * they come to: an answer whose sign is the order of two arguments, held at nought, is their
     * equality ({@link BoundOperationFacts#statesTheOrderOfItsArguments}), and a sum or difference
     * of totals is a form over them — so {@code Decimal.compare(d, c) == 0} says {@code d == c}.
     * What is left has to be one total less another of the same list, at two cases, and nothing
     * beside: a constant or a third total is another rule.
     *
     * <p>And it adds nothing that ends a run to what the totals work out: an operation the library
     * says may stop is a rule over the totals that the rule written as their equality is not, where
     * it stops. {@code Decimal.subtract(d, c) == 0.0m} is one, since a decimal's difference may have
     * no place ({@link WhatARunMayEndFor}).
     */
    static Stated read(StatedComparison stated) {
        if (stated.relationUnder(true) != Rel.EQ) {
            return null;
        }
        Core left = stated.left();
        Core right = stated.right();
        List<Core> ordered = orderAtNought(left, right);
        if (ordered == null) {
            ordered = orderAtNought(right, left);
        }
        if (ordered != null) {
            left = ordered.get(0);
            right = ordered.get(1);
        }
        Map<BindingId, Core> lists = new HashMap<>();
        LinearForm<Side> one = totals(left, lists);
        LinearForm<Side> other = one == null ? null : totals(right, lists);
        LinearForm<Side> form = other == null ? null : one.minus(other).orNull();
        if (form == null || !form.constant().isZero() || form.coefs().size() != 2) {
            return null;
        }
        Side more = null;
        Side less = null;
        ExactRatio by = null;
        for (var term : form.coefs().entrySet()) {
            if (by == null) {
                more = term.getKey();
                by = term.getValue();
            } else if (term.getValue().equals(by.negated())) {
                less = term.getKey();
            }
        }
        if (less == null || more.at().equals(less.at()) || !more.field().equals(less.field())
                || !more.number().equals(less.number()) || !more.list().equals(less.list())) {
            return null;
        }
        return new Stated(lists.get(more.list()), more.field(), more.number(), more.at(), less.at());
    }

    /**
     * The two arguments of {@code sign}, the greater first, where it answers the order of the two
     * and {@code nought} is nought — or null where it is no such comparison.
     */
    private static List<Core> orderAtNought(Core sign, Core nought) {
        AnOperationApplied applied = AnOperationApplied.of(sign);
        BoundOperationFact.StatesTheOrderOfItsArguments order = applied == null ? null
                : DefaultBoundOperationFacts.get().statesTheOrderOfItsArguments(
                        applied.operation());
        if (order == null || !(Core.withoutStanding(nought) instanceof Core.Int zero)
                || zero.value() != 0 || !WhatARunMayEndFor.itself(sign).endsNone()) {
            return null;
        }
        Core greater = applied.argument(order.greater());
        Core lesser = applied.argument(order.lesser());
        return greater == null || lesser == null ? null : List.of(greater, lesser);
    }

    /** {@code e} as a sum of totals and constants, or null where it is anything else. */
    private static LinearForm<Side> totals(Core e, Map<BindingId, Core> lists) {
        Core bare = Core.withoutStanding(e);
        if (bare instanceof Core.Decimal number) {
            return LinearForm.constant(ExactRatio.of(number.value()));
        }
        if (bare instanceof Core.Int number) {
            return LinearForm.constant(ExactRatio.of(number.value()));
        }
        AnOperationApplied applied = AnOperationApplied.of(bare);
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        // Only an addition the library says ends no run: one that stops where its answer has no
        // place stops on totals the rule written as their order does not, and is another rule
        // there. A decimal's sum is one of those.
        if (applied != null && applied.args().size() == 2
                && WhatARunMayEndFor.itself(bare).endsNone()
                && (facts.computing(BinOp.ADD).contains(applied.operation())
                        || facts.computing(BinOp.SUB).contains(applied.operation()))) {
            LinearForm<Side> first = totals(applied.args().get(0), lists);
            LinearForm<Side> second = first == null ? null : totals(applied.args().get(1), lists);
            if (second == null) {
                return null;
            }
            return (facts.computing(BinOp.ADD).contains(applied.operation())
                    ? first.plus(second) : first.minus(second)).orNull();
        }
        Side side = side(bare, lists);
        return side == null ? null : LinearForm.atom(side);
    }

    /**
     * A total of a list, adding one number of an element where a field of it is a case: the walk
     * adds it under that condition, or walks only the elements a filter kept by it.
     *
     * <p>The filter as the library says it puts its answer together — each element where the
     * closure holds of it, and nothing where it does not
     * ({@link PieceOfAnElement#THE_ELEMENT_WHERE_IT_HOLDS}) — so a total of what it kept is the
     * total of the elements meeting its condition. One condition and not two: a walk both filtered
     * and conditioned adds under both, which is no case of one field.
     */
    private static Side side(Core e, Map<BindingId, Core> lists) {
        Map<BindingId, Core> given = new HashMap<>();
        Core walk = LetBound.resolved(e, given);
        if (!(AnOperationApplied.of(walk) instanceof AnOperationApplied(var operation, var args))
                || !operation.equals(FOLD) || args.size() != 4
                || !(LetBound.resolved(args.get(0), given) instanceof Core.Block step)
                || step.params().size() != 2
                || !(LetBound.resolved(args.get(1), given) instanceof Core.Decimal seed)
                || seed.value().signum() != 0) {
            return null;
        }
        Core walked = LetBound.resolved(args.get(2), given);
        AtACase kept = null;
        if (AnOperationApplied.of(walked) instanceof AnOperationApplied filter
                && DefaultBoundOperationFacts.get().assembles(filter.operation())
                        instanceof BoundOperationFacts.Assembled assembled
                && assembled.piece() == PieceOfAnElement.THE_ELEMENT_WHERE_IT_HOLDS
                && filter.argument(assembled.closure()) != null
                && LetBound.resolved(filter.argument(assembled.closure()), given)
                        instanceof Core.Block keep
                && keep.params().size() == 1
                // The filter and its condition ending no run, as the step's own condition does in
                // the walk that adds under it: what is kept is then every element meeting it.
                && WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(walked).endsNone()
                && WhatARunMayEndFor.endsNoneBeneath(keep.body())) {
            kept = caseOf(keep.body(), keep.params().getFirst().binding(), given);
            if (kept == null || filter.argument(assembled.source()) == null) {
                return null;
            }
            walked = LetBound.resolved(filter.argument(assembled.source()), given);
        }
        if (!(walked instanceof Core.Read list)) {
            return null;
        }
        BindingId total = step.params().get(0).binding();
        BindingId element = step.params().get(1).binding();
        Core adds = Core.withoutStanding(step.body());
        AtACase where = null;
        if (adds instanceof Core.If choice) {
            if (!(Core.withoutStanding(choice.els()) instanceof Core.Read same)
                    || !same.binding().equals(total)) {
                return null;
            }
            where = caseOf(choice.cond(), element, given);
            adds = Core.withoutStanding(choice.then());
            if (where == null) {
                return null;
            }
        }
        if ((where == null) == (kept == null)) {
            return null;
        }
        AtACase at = where != null ? where : kept;
        // The number added to the total, in either order.
        if (!(AnOperationApplied.of(adds) instanceof AnOperationApplied(var added, var parts))
                || !DefaultBoundOperationFacts.get().computing(BinOp.ADD).contains(added)
                || parts.size() != 2) {
            return null;
        }
        List<String> number = isTheTotal(parts.get(0), total) ? stepsFrom(parts.get(1), element)
                : isTheTotal(parts.get(1), total) ? stepsFrom(parts.get(0), element) : null;
        if (number == null || number.isEmpty()) {
            return null;
        }
        lists.putIfAbsent(list.binding(), list);
        return new Side(list.binding(), at.field(), number, at.at());
    }

    /** The field of the element bound at {@code element} that {@code condition} holds equal to a
     *  case, and the case — or null where it says anything else. */
    private static AtACase caseOf(Core condition, BindingId element, Map<BindingId, Core> given) {
        if (!(Core.withoutStanding(condition) instanceof Core.Binary at) || at.op() != BinOp.EQ) {
            return null;
        }
        List<String> field = stepsFrom(at.left(), element);
        Core named = at.right();
        if (field == null) {
            field = stepsFrom(at.right(), element);
            named = at.left();
        }
        return field == null || field.size() != 1
                || !(LetBound.resolved(named, given) instanceof Core.UnitValue unit) ? null
                : new AtACase(field.getFirst(), unit.data());
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
        // Only a record all of whose rules were read: the list is built balanced and nothing else
        // is asked of it, and a rule nothing was made of may keep its elements apart, bound how
        // many it holds or relate it to another field.
        if (rules == null || !rules.readInFull()) {
            return Map.of();
        }
        Map<RuleKey, List<Requirement>> out = new LinkedHashMap<>();
        Map<RuleKey, List<InvariantStatement>> builtFor = new HashMap<>();
        for (InvariantStatement one : rules.statements()) {
            if (!(one instanceof InvariantStatement.BalancesSides it)) {
                continue;
            }
            RuleKey where = rules.fieldAt(it.balanced().list());
            if (where != null) {
                out.computeIfAbsent(where, _ -> new ArrayList<>())
                        .add(new Requirement(it.balanced().field(), it.balanced().number(),
                                it.balanced().one(), it.balanced().other()));
                builtFor.computeIfAbsent(where, _ -> new ArrayList<>()).add(one);
            }
        }
        Map<RuleKey, List<Requirement>> held = new LinkedHashMap<>();
        out.forEach((where, requirements) -> {
            // And a list no statement but those built for reads from: it is built balanced, and a
            // statement asking anything else of it, recognised or not and however it is written,
            // is one it is built without knowing of. How many it holds is the range its count
            // already has, and is not another statement.
            if (buildable(where, requirements) && elementsStandAlone(named, where, source)
                    && !rules.readBesides(builtFor.get(where), where.steps().getFirst())) {
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
