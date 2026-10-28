package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * The values a list may be grown by at a position of one element type when no row ran that type:
 * what the compiler stands for the type with, and the whole numbers beside them.
 *
 * <p>These are proposals and not observations, so they are kept apart from
 * {@link InputsRowsRanWith}: whether one of them answers, and answers differently, is what running
 * the candidate says. A type whose representatives are not a literal, or a newtype of one, offers
 * nothing here.
 */
final class ElementsOfAType {

    private ElementsOfAType() {}

    /** The representatives of {@code element}, then the whole numbers one step from each. */
    static List<ObservedValue> of(MeasuredInput subject, Type element) {
        TypeView view = TypeView.of(element, subject.ruleReading().source().inners(),
                subject.ruleReading().source().symbols(), subject.ruleReading().source().kinds(),
                subject.ruleReading().source().sums());
        List<ObservedValue> stood = new ArrayList<>();
        for (FixtureTemplate each : subject.representativesHolding(element,
                FieldDomains.ConstructionLimits.NONE).values()) {
            ObservedValue inside = literalOf(each.value());
            if (inside != null) {
                ObservedValue value = ObservedValue.wrapped(view.wrappers(), inside);
                if (!stood.contains(value)) {
                    stood.add(value);
                }
            }
        }
        List<ObservedValue> out = new ArrayList<>(stood);
        for (ObservedValue each : stood) {
            for (Iterator<ObservedValue> near = NearbyValues.of(each, element,
                    subject.ruleReading()); near.hasNext(); ) {
                ObservedValue value = near.next();
                if (!out.contains(value)) {
                    out.add(value);
                }
            }
        }
        return List.copyOf(out);
    }

    /** The scalar a fixture writes, under the single-argument constructions of a newtype; null for
     *  anything else. */
    private static ObservedValue literalOf(Hir.Expr written) {
        return switch (written) {
            case Hir.IntLit lit -> new ObservedValue.Integer(lit.value());
            case Hir.StringLit lit -> new ObservedValue.Text(lit.value());
            case Hir.DecimalLit lit -> new ObservedValue.Decimal(lit.value());
            case Hir.BoolLit lit -> new ObservedValue.Bool(lit.value());
            case Hir.Neg(Hir.IntLit lit, var _, var _) -> new ObservedValue.Integer(-lit.value());
            case Hir.Neg(Hir.DecimalLit lit, var _, var _) ->
                    new ObservedValue.Decimal(lit.value().negate());
            case Hir.Apply apply when apply.args().size() == 1 -> literalOf(apply.args().getFirst());
            default -> null;
        };
    }
}
