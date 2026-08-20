package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.math.BigDecimal;
import java.util.List;

/**
 * How a value a rule named is recognised in a row and written back.
 *
 * <p>Which values those are, and whether they stand at the position at all, is the reading's
 * ({@code Distinctions#ofValues}). What is here is the other half: a class asking whether an
 * observation is that value, and a fixture writing one.
 */
final class ValueClasses {

    /**
     * One named value's class.
     *
     * <p>The reading has already settled that the value stands at this position, so a value this
     * cannot write is the two of them disagreeing rather than a division to give up on — said
     * loudly, because a class quietly missing here is a distinction the model states going missing
     * from every measure at once.
     *
     * @param view the position as it is written, so that a value is classified under the names it
     *             wears and written back under them
     */
    static PartitionClass classAt(Value value, TypeView view, List<TypeSymbol> worn,
                                  Symbols symbols) {
        FixtureTemplate bare = written(value, view.declared(), symbols);
        if (bare == null) {
            throw new IllegalStateException(
                    "the reading of `" + Type.show(view.declared()) + "` states a distinction at a"
                            + " value this cannot write; the two readings of one position disagree"
                            + " about what stands at it");
        }
        Classifier is = Classifier.under(worn, Classifier.byShape(seen -> holds(seen, value)));
        FixtureTemplate stands = Witnesses.wrapped(view.declared(), bare, symbols);
        return (stands == null
                // A name the position wears that nothing here writes. The class is the position's
                // either way and a row already sitting in it still covers it; what is absent is the
                // offer of a new row (issue #696).
                ? PartitionClass.ungeneratable(bare.text(), bare.text(), is,
                        "nothing here can write a value of this position")
                : PartitionClass.of(bare.text(), bare.text(), is,
                        RepresentativeSource.of(stands)))
                // The one value it was made from, which is the whole of what it holds.
                .holding(ValueSet.just(value));
    }

    /**
     * The value as a row writes it, or null where this does not write values of that kind.
     *
     * <p>Which of {@code Int} and {@code Decimal} a number is written as is the position's own type
     * to say. The two are never compared with each other (E1319), so a position is written about in
     * one of them and never in both.
     */
    private static FixtureTemplate written(Value value, Type type, Symbols symbols) {
        return switch (value) {
            case Value.Text text -> FixtureTemplate.string(text.value());
            case Value.Truth truth -> FixtureTemplate.bool(truth.value());
            case Value.Number number -> TypeOps.numericBase(type, symbols) == Type.DECIMAL
                    ? FixtureTemplate.decimal(number.value())
                    : whole(number.value());
            case Value.Case _ -> null;
        };
    }

    /** A whole number, or null where the number the rules name is not one. */
    private static FixtureTemplate whole(BigDecimal value) {
        try {
            return FixtureTemplate.integer(value.longValueExact());
        } catch (ArithmeticException e) {
            return null;
        }
    }

    /**
     * Whether an observed value is the one this class is of.
     *
     * <p>Bare, without the names the position wears: a classifier that reads through names takes off
     * the ones that are there and answers about the rest, so a value handed over as it stands is
     * answered by the same classifier a row is.
     */
    private static boolean holds(ObservedValue seen, Value value) {
        return switch (value) {
            case Value.Text text ->
                    seen instanceof ObservedValue.Text it && it.value().equals(text.value());
            case Value.Truth truth ->
                    seen instanceof ObservedValue.Bool it && it.value() == truth.value();
            // Compared as numbers and not as writings of them. `1.0m` and `1.00m` are one value
            // where they are written, and the reading that named this class already holds them as
            // one (`Value.Number`).
            case Value.Number number -> switch (seen) {
                case ObservedValue.Integer it ->
                        BigDecimal.valueOf(it.value()).compareTo(number.value()) == 0;
                case ObservedValue.Decimal it -> it.value().compareTo(number.value()) == 0;
                default -> false;
            };
            case Value.Case one -> switch (seen) {
                case ObservedValue.Unit it -> one.data().equals(it.type());
                case ObservedValue.Constructed it -> one.data().equals(it.type());
                default -> false;
            };
        };
    }

    private ValueClasses() {}
}
