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
import java.util.ArrayList;
import java.util.List;

/**
 * The classes a position has where its rules name the values it may hold.
 *
 * <p>The same division a sum states, written another way. {@code data Gender = A | B} and
 * {@code data Gender = String invariant value == "A" || value == "B"} divide their position exactly
 * alike — every value of it is one or the other, and a row sits in one of them — and the second was
 * read by nothing, so a report said the model draws no distinction there.
 *
 * <p>One class per value and no complement. Everything outside what an invariant admits is refused
 * at construction (E1903), so there is no class on the other side to cover — the same restraint a
 * bounded newtype gets, where the bound is a line and not a pair of classes. A {@code guard} that
 * singles a value out is the other case and does have a complement ({@code Partitions#singledClasses}):
 * there the values on the far side exist and a row can be written at one.
 *
 * <p>Only where the values are named. {@link ValueSet.Cofinite} says which values are refused and
 * names none of the ones left, so it divides nothing here — {@code value /= "A"} leaves one class
 * of everything else, which is the position undivided.
 *
 * <p>Nothing here reads how much of the rules was taken in. A set arrived at from part of them is
 * still a set of values the model singled out, and the classes are the same classes; what the
 * completeness beside it decides is what may be concluded from the <em>absence</em> of a set, which
 * is {@link LocalPartition}'s to say.
 */
final class ValueClasses {

    /**
     * The classes {@code admitted} gives the position, or nothing where it gives none.
     *
     * @param view the position as it is written, so that a value is classified under the names it
     *             wears and written back under them
     */
    static List<PartitionClass> of(ValueSet admitted, TypeView view, Symbols symbols) {
        if (!(admitted instanceof ValueSet.Finite finite) || finite.values().isEmpty()) {
            return List.of();
        }
        List<TypeSymbol> worn = view.wrappers().stream().map(TypeOps.Layer::named).toList();
        List<PartitionClass> classes = new ArrayList<>();
        for (Value value : finite.values()) {
            PartitionClass here = classAt(value, view, worn, symbols);
            if (here == null) {
                // A value this producer has no way to write down. Nothing is dropped by leaving it
                // out: the reading that named it is the one that divides the position, so a
                // division this can only half describe is one it does not make.
                return List.of();
            }
            classes.add(here);
        }
        return List.copyOf(classes);
    }

    /** One value's class, or null where nothing here can turn the value into one. */
    private static PartitionClass classAt(Value value, TypeView view, List<TypeSymbol> worn,
                                          Symbols symbols) {
        FixtureTemplate bare = written(value, view.declared(), symbols);
        if (bare == null) {
            return null;
        }
        Classifier is = Classifier.under(worn, Classifier.byShape(seen -> holds(seen, value)));
        FixtureTemplate stands = Witnesses.wrapped(view.declared(), bare, symbols);
        return stands == null
                // A name the position wears that nothing here writes. The class is the position's
                // either way and a row already sitting in it still covers it; what is absent is the
                // offer of a new row (issue #696).
                ? PartitionClass.ungeneratable(bare.text(), bare.text(), is,
                        "nothing here can write a value of this position")
                : PartitionClass.of(bare.text(), bare.text(), is,
                        RepresentativeSource.of(stands));
    }

    /**
     * The value as a row writes it, or null where this does not write values of that kind.
     *
     * <p>A case of an enumeration is not one of these. What tells two cases apart is which
     * declaration each is, and the reading that names the cases of a position is the one that reads
     * its type ({@link PartitionClasses}) — so a case arriving here is a value the declared reading
     * has already made a class of, and a second class for it would be the same class twice.
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

    /** A whole number, or null where the number the rules name is not one. A rule naming a value an
     *  {@code Int} cannot hold admits nothing, which is a refusal of the declaration rather than a
     *  class here. */
    private static FixtureTemplate whole(BigDecimal value) {
        try {
            return FixtureTemplate.integer(value.longValueExact());
        } catch (ArithmeticException e) {
            return null;
        }
    }

    /** Whether an observed value is the one this class is of. */
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
