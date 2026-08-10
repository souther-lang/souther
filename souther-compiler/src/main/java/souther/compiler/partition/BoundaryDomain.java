package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

import java.math.BigDecimal;
import java.util.Optional;

/**
 * What a type can say about the values next to a boundary.
 *
 * <p>Asking for "the value just over the threshold" is asking the type, not the threshold. A whole
 * number has a next one; a decimal, in general, does not — {@code 100000.000…1} is not a value the
 * type names, and inventing an epsilon would test a rule the model never stated. Where a type cannot
 * answer, the boundary itself is still worth a row and the value beside it is reported as
 * not derivable rather than made up.
 */
public interface BoundaryDomain {

    Optional<ObservedValue> successor(ObservedValue value);

    Optional<ObservedValue> predecessor(ObservedValue value);

    Optional<ObservedValue> midpoint(ObservedValue low, ObservedValue high);

    /** Souther's {@code Int}: a whole number, so both neighbours exist. */
    BoundaryDomain INT = new BoundaryDomain() {
        @Override
        public Optional<ObservedValue> successor(ObservedValue value) {
            return value instanceof ObservedValue.Integer i && i.value() != Long.MAX_VALUE
                    ? Optional.of(new ObservedValue.Integer(i.value() + 1)) : Optional.empty();
        }

        @Override
        public Optional<ObservedValue> predecessor(ObservedValue value) {
            return value instanceof ObservedValue.Integer i && i.value() != Long.MIN_VALUE
                    ? Optional.of(new ObservedValue.Integer(i.value() - 1)) : Optional.empty();
        }

        @Override
        public Optional<ObservedValue> midpoint(ObservedValue low, ObservedValue high) {
            if (!(low instanceof ObservedValue.Integer l)
                    || !(high instanceof ObservedValue.Integer h)) {
                return Optional.empty();
            }
            long mid = l.value() + (h.value() - l.value()) / 2;
            return Optional.of(new ObservedValue.Integer(mid));
        }
    };

    /**
     * Souther's {@code Decimal}. A neighbour needs a smallest step, and the type does not carry one,
     * so there is none to give. A midpoint is an ordinary decimal and is given.
     */
    BoundaryDomain DECIMAL = new BoundaryDomain() {
        @Override
        public Optional<ObservedValue> successor(ObservedValue value) {
            return Optional.empty();
        }

        @Override
        public Optional<ObservedValue> predecessor(ObservedValue value) {
            return Optional.empty();
        }

        @Override
        public Optional<ObservedValue> midpoint(ObservedValue low, ObservedValue high) {
            if (!(low instanceof ObservedValue.Decimal l)
                    || !(high instanceof ObservedValue.Decimal h)) {
                return Optional.empty();
            }
            return Optional.of(new ObservedValue.Decimal(
                    l.value().add(h.value()).divide(BigDecimal.valueOf(2))));
        }
    };

    /**
     * Souther's {@code Date}: a whole number of days, so both neighbours exist.
     *
     * <p>The neighbour of a date is a date. What steps is the day it counts to, and what comes back
     * is written the way a model writes one — a report and a row show the date, never the count.
     */
    BoundaryDomain DATE = new BoundaryDomain() {
        @Override
        public Optional<ObservedValue> successor(ObservedValue value) {
            return stepped(value, 1);
        }

        @Override
        public Optional<ObservedValue> predecessor(ObservedValue value) {
            return stepped(value, -1);
        }

        @Override
        public Optional<ObservedValue> midpoint(ObservedValue low, ObservedValue high) {
            BigDecimal from = dayOf(low);
            BigDecimal to = dayOf(high);
            return from == null || to == null ? Optional.empty()
                    : Optional.of(new ObservedValue.Temporal(Dates.written(
                            from.add(to.subtract(from).divide(BigDecimal.valueOf(2))))));
        }

        private Optional<ObservedValue> stepped(ObservedValue value, int by) {
            BigDecimal day = dayOf(value);
            return day == null ? Optional.empty()
                    : Optional.of(new ObservedValue.Temporal(
                            Dates.written(day.add(BigDecimal.valueOf(by)))));
        }

        private BigDecimal dayOf(ObservedValue value) {
            return value instanceof ObservedValue.Temporal t ? Dates.dayOf(t.iso()) : null;
        }
    };

    /** Nothing has a neighbour here. */
    BoundaryDomain NONE = new BoundaryDomain() {
        @Override
        public Optional<ObservedValue> successor(ObservedValue value) {
            return Optional.empty();
        }

        @Override
        public Optional<ObservedValue> predecessor(ObservedValue value) {
            return Optional.empty();
        }

        @Override
        public Optional<ObservedValue> midpoint(ObservedValue low, ObservedValue high) {
            return Optional.empty();
        }
    };
}
