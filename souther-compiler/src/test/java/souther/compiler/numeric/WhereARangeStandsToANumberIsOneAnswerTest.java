package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Whether the values a range holds stand in a relation to a number is one answer of the range
 * ({@link NumericDomain.Bounds#stands}): every one of them, none of them, or some and not others.
 *
 * <p>Held against the relation itself, value by value. Over every range of whole numbers between
 * two small ends and every relation, what the range answers is what reading each value it holds
 * through {@link Rel#holds} comes to — so a range of just the number is equal to it and not unequal,
 * which an answer read through the range of a relation's denial could not say of equality.
 */
class WhereARangeStandsToANumberIsOneAnswerTest {

    @Test
    void aRangeOfWholeNumbersAnswersAsItsValuesDo() {
        List<String> wrong = new ArrayList<>();
        for (long least = -2; least <= 2; least++) {
            for (long most = least; most <= 2; most++) {
                for (long against = -1; against <= 1; against++) {
                    for (Rel rel : Rel.values()) {
                        Boolean expected = valueByValue(rel, against, least, most);
                        Boolean answered = new NumericDomain.Bounds(
                                Endpoint.inclusive(Count.of(least)),
                                Endpoint.inclusive(Count.of(most)))
                                .stands(rel, Count.of(against));
                        if (!Objects.equals(expected, answered)) {
                            wrong.add("[" + least + ", " + most + "] " + rel + " " + against
                                    + ": " + answered + ", by its values " + expected);
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    @Test
    void aRangeWithNoEndOnASideHoldsValuesPastAnyNumberThere() {
        NumericDomain.Bounds fromOne = new NumericDomain.Bounds(Endpoint.inclusive(Count.of(1)),
                null);
        assertEquals(true, fromOne.stands(Rel.GT, Count.of(0)));
        assertEquals(false, fromOne.stands(Rel.EQ, Count.of(0)));
        assertNull(fromOne.stands(Rel.GT, Count.of(5)));
        assertNull(NumericDomain.Bounds.OPEN.stands(Rel.NE, Count.of(0)));
        assertEquals(true, new NumericDomain.Bounds(null,
                Endpoint.exclusive(Count.of(new BigDecimal("0.5")))).stands(Rel.NE, Count.of(1)));
    }

    /** True where every value from {@code least} to {@code most} stands {@code rel} to
     *  {@code against}, false where none does, and null otherwise. */
    private static Boolean valueByValue(Rel rel, long against, long least, long most) {
        boolean every = true;
        boolean some = false;
        for (long value = least; value <= most; value++) {
            boolean holds = rel.holds(Long.compare(value, against));
            every &= holds;
            some |= holds;
        }
        return every ? Boolean.TRUE : !some ? Boolean.FALSE : null;
    }
}
