package souther.runtime;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

/**
 * {@link Representations} against a written-form oracle. The contract this pins is that comparing
 * two external forms answers zero exactly when they are the same JSON value — so the corpus below
 * holds every kind an encoder emits, and the laws are checked over all of its pairs and triples
 * rather than over a hand-picked few.
 */
class RepresentationsTest {

    /**
     * One value of every kind, plus the pairs that make the rule visible: a Long and a Decimal that
     * write the same, three Decimals that are one amount and three forms, a supplementary character
     * against a BMP one that is the larger code unit and the smaller code point, and two objects
     * that differ only in the order their members were put.
     */
    private static final List<@Nullable Object> CORPUS = Arrays.asList(
            null,
            false,
            true,
            0L,
            1L,
            2L,
            -5L,
            Long.MAX_VALUE,
            new BigDecimal("1"),
            new BigDecimal("1.0"),
            new BigDecimal("1.00"),
            new BigDecimal("2.5"),
            new BigDecimal("-3"),
            new BigDecimal("10"),
            new BigDecimal("1E+1"),        // the same amount as 10, and not the same number written
            "",
            "a",
            "b",
            "aa",
            "Aa",
            "BB",
            "😀",                          // U+1F600, a surrogate pair
            "",                                // U+E000: the larger code unit, the smaller code point
            List.of(),
            List.of(1L),
            List.of(1L, 2L),
            List.of(2L),
            List.of("a"),
            object(),
            object("a", 1L),
            object("a", 1L, "b", 2L),
            object("b", 2L, "a", 1L),                // the same object, put the other way round
            object("a", List.of(1L, object("a", true))),
            Arrays.asList(1L, null),                 // null is a member, not only a whole value
            object("a", null, "b", 1L),              // written null, which is not the same object as
            object("b", 1L, "c", 2L));               // one whose member is absent

    // === a number is written as its amount ===

    @Test
    void aNumberIsWrittenAsItsAmountAndNotAsTheScaleItArrivedWith() {
        assertEquals("1", Representations.canonicalNumber(new BigDecimal("1.00")).toString());
        assertEquals("1.5", Representations.canonicalNumber(new BigDecimal("1.50")).toString());
        assertEquals("-3", Representations.canonicalNumber(new BigDecimal("-3.000")).toString());
        assertEquals("0", Representations.canonicalNumber(new BigDecimal("0.000")).toString());
    }

    @Test
    void aRoundAmountIsWrittenOutRatherThanInExponentForm() {
        // stripTrailingZeros alone answers 1E+2 for a hundred, and Jackson writes a BigDecimal as
        // its toString, so the exponent would reach the wire.
        assertEquals("100", Representations.canonicalNumber(new BigDecimal("100")).toString());
        assertEquals("100", Representations.canonicalNumber(new BigDecimal("100.00")).toString());
        assertEquals("1000000", Representations.canonicalNumber(new BigDecimal("1.0E+6")).toString());
    }

    @Test
    void anExponentTooLongToSpellOutKeepsIt() {
        // 1E+1000000 is eleven characters and a million and one digits, so spelling every amount out
        // would let a value that costs nothing to name ask for a megabyte of JSON.
        BigDecimal huge = new BigDecimal("1E+1000000");
        BigDecimal written = Representations.canonicalNumber(huge);
        assertEquals(0, huge.compareTo(written), "the same amount either way");
        assertTrue(written.toString().length() <= 1000,
                "written as " + written.toString().length() + " characters");
    }

    @Test
    void theLongestExponentSpeltOutIsAThousandDigits() {
        // The cut is on the expansion, not on the output: what a value already carries it keeps, and
        // a sign is not a digit, so -1E+999 is written out as 1001 characters.
        assertEquals(1000, Representations.canonicalNumber(new BigDecimal("1E+999")).toString().length());
        assertEquals("1E+1000", Representations.canonicalNumber(new BigDecimal("1E+1000")).toString());
        assertEquals(1001, Representations.canonicalNumber(new BigDecimal("-1E+999")).toString().length());
    }

    @Test
    void howLongAnAmountIsWrittenIsDecidedByTheAmountAndNotByHowItArrived() {
        // Both are 10^1000000, written two ways. The cut has to fall on the amount, or the same
        // value would cross the boundary as two numbers again.
        assertEquals(Representations.canonicalNumber(new BigDecimal("1E+1000000")),
                Representations.canonicalNumber(new BigDecimal("10E+999999")));
        assertEquals(Representations.canonicalNumber(new BigDecimal("100.00")),
                Representations.canonicalNumber(new BigDecimal("1E+2")));
    }

    /** The amounts that make the number rules visible, including both ends of what a scale may be. */
    private static final List<BigDecimal> AMOUNTS = Arrays.asList(
            new BigDecimal("0"), new BigDecimal("0.000"), new BigDecimal("1"), new BigDecimal("1.00"),
            new BigDecimal("-3.000"), new BigDecimal("100"), new BigDecimal("1.0E+6"),
            new BigDecimal("1E+999"), new BigDecimal("-1E+999"), new BigDecimal("1E+1000"),
            new BigDecimal("1E+1000000"), new BigDecimal("10E+999999"),
            new BigDecimal(BigInteger.ONE, Integer.MAX_VALUE),
            new BigDecimal(BigInteger.ONE, Integer.MIN_VALUE),
            new BigDecimal(BigInteger.TEN, Integer.MIN_VALUE),
            new BigDecimal(BigInteger.valueOf(100), Integer.MIN_VALUE + 1),
            new BigDecimal(BigInteger.ZERO, Integer.MIN_VALUE));

    @Test
    void everyAmountHasAFormIncludingTheOnesAtTheEndsOfTheScale() {
        // The rule is a function on amounts, so there is no amount it declines to answer for. Both
        // ends are reachable: stripping a trailing zero off a scale already at the floor asks for a
        // scale the type cannot say, and counting the digits of one asks for more than an int holds.
        for (BigDecimal amount : AMOUNTS) {
            assertDoesNotThrow(() -> Representations.canonicalNumber(amount), amount::toString);
        }
    }

    @Test
    void aFormIsTheSameAmountAsWhatItWasMadeFrom() {
        for (BigDecimal amount : AMOUNTS) {
            assertEquals(0, Representations.canonicalNumber(amount).compareTo(amount),
                    () -> "rewrote " + amount);
        }
    }

    @Test
    void makingAFormOfAFormChangesNothing() {
        for (BigDecimal amount : AMOUNTS) {
            BigDecimal once = Representations.canonicalNumber(amount);
            assertEquals(once, Representations.canonicalNumber(once), () -> "unsettled at " + amount);
        }
    }

    @Test
    void amountsThatAreOneAmountHaveOneFormWhicheverEndOfTheScaleTheySitAt() {
        for (BigDecimal a : AMOUNTS) {
            for (BigDecimal b : AMOUNTS) {
                if (a.compareTo(b) == 0) {
                    assertEquals(Representations.canonicalNumber(a), Representations.canonicalNumber(b),
                            () -> "one amount, two forms: " + a + " and " + b);
                }
            }
        }
    }

    @Test
    void twoAmountsThatAreOneAmountAreWrittenTheOneWay() {
        assertEquals(Representations.canonicalNumber(new BigDecimal("1.0")),
                Representations.canonicalNumber(new BigDecimal("1.00")));
        assertEquals(0, Representations.compareExternalForms(
                Representations.canonicalNumber(new BigDecimal("1.0")),
                Representations.canonicalNumber(new BigDecimal("1.00"))));
    }

    // === the kinds ===

    @Test
    void theKindsAreOrderedNullFalseTrueNumberStringArrayObject() {
        List<@Nullable Object> ascending = Arrays.asList(null, false, true, 0L, "", List.of(), object());
        for (int i = 0; i < ascending.size() - 1; i++) {
            assertTrue(Representations.compareExternalForms(ascending.get(i), ascending.get(i + 1)) < 0,
                    ascending.get(i) + " must come before " + ascending.get(i + 1));
        }
    }

    // === numbers ===

    @Test
    void numbersOrderByAmountAndThenByTheFormTheyAreWrittenIn() {
        assertTrue(Representations.compareExternalForms(new BigDecimal("1"), new BigDecimal("2.5")) < 0);
        // one amount, three forms: the amount cannot separate them, so the written form does
        assertTrue(Representations.compareExternalForms(new BigDecimal("1"), new BigDecimal("1.0")) < 0);
        assertTrue(Representations.compareExternalForms(new BigDecimal("1.0"), new BigDecimal("1.00")) < 0);
        // and the amount still decides first: 1.00 is written longer than 2.5 and is still smaller
        assertTrue(Representations.compareExternalForms(new BigDecimal("1.00"), new BigDecimal("2.5")) < 0);
    }

    @Test
    void aLongAndADecimalThatWriteTheSameAreOneForm() {
        assertEquals(0, Representations.compareExternalForms(1L, new BigDecimal("1")));
    }

    @Test
    void aLongAndADecimalOfTheSameAmountWrittenDifferentlyAreTwoForms() {
        assertTrue(Representations.compareExternalForms(1L, new BigDecimal("1.0")) != 0);
    }

    // === strings ===

    @Test
    void stringsOrderByUtf16CodeUnit() {
        // U+1F600 is the larger code point, and its leading surrogate D83D is the smaller code unit.
        // The boundary order is the code unit one, so the emoji comes first.
        assertTrue(Representations.compareExternalForms("😀", "") < 0);
        assertTrue(Representations.compareExternalForms("Aa", "BB") < 0);
        assertTrue(Representations.compareExternalForms("a", "aa") < 0);
    }

    // === arrays ===

    @Test
    void arraysOrderElementByElementAndTheShorterOneFirst() {
        assertTrue(Representations.compareExternalForms(List.of(1L), List.of(2L)) < 0);
        assertTrue(Representations.compareExternalForms(List.of(1L), List.of(1L, 2L)) < 0);
        assertTrue(Representations.compareExternalForms(List.of(), List.of(1L)) < 0);
    }

    @Test
    void theOrderOfAnArrayIsPartOfWhatItIs() {
        assertTrue(Representations.compareExternalForms(List.of(1L, 2L), List.of(2L, 1L)) != 0);
    }

    // === objects ===

    @Test
    void theMemberOrderOfAnObjectIsNotPartOfWhatItIs() {
        assertEquals(0, Representations.compareExternalForms(
                object("a", 1L, "b", 2L), object("b", 2L, "a", 1L)));
    }

    @Test
    void objectsOrderByTheirKeysBeforeTheirValues() {
        assertTrue(Representations.compareExternalForms(object("a", 9L), object("b", 1L)) < 0);
        assertTrue(Representations.compareExternalForms(object("a", 1L), object("a", 2L)) < 0);
        assertTrue(Representations.compareExternalForms(object("a", 1L), object("a", 1L, "b", 2L)) < 0);
    }

    @Test
    void anObjectIsReadTheSameWhicheverMapCarriesIt() {
        assertEquals(0, Representations.compareExternalForms(
                object("a", 1L, "b", 2L), new TreeMap<>(Map.of("a", 1L, "b", 2L))));
    }

    // === the law the whole thing rests on, both directions apart ===

    @Test
    void answeringZeroMeansTheTwoAreWrittenTheSame() {
        forEachPair((a, b) -> {
            if (Representations.compareExternalForms(a, b) == 0) {
                assertEquals(written(a), written(b),
                        "compared equal but written differently: " + written(a) + " / " + written(b));
            }
        });
    }

    @Test
    void beingWrittenTheSameMeansAnsweringZero() {
        forEachPair((a, b) -> {
            if (written(a).equals(written(b))) {
                assertEquals(0, Representations.compareExternalForms(a, b),
                        "written the same but compared apart: " + written(a));
            }
        });
    }

    @Test
    void representationEqualsAgreesWithAnsweringZero() {
        forEachPair((a, b) -> assertEquals(Representations.compareExternalForms(a, b) == 0,
                Representations.representationEquals(a, b),
                "disagreed about " + written(a) + " / " + written(b)));
    }

    // === it is a total order ===

    @Test
    void theOrderIsAntisymmetric() {
        forEachPair((a, b) -> assertEquals(
                Integer.signum(Representations.compareExternalForms(a, b)),
                -Integer.signum(Representations.compareExternalForms(b, a)),
                written(a) + " / " + written(b)));
    }

    @Test
    void theOrderIsTransitive() {
        for (@Nullable Object a : CORPUS) {
            for (@Nullable Object b : CORPUS) {
                if (Representations.compareExternalForms(a, b) > 0) {
                    continue;
                }
                for (@Nullable Object c : CORPUS) {
                    if (Representations.compareExternalForms(b, c) <= 0) {
                        assertTrue(Representations.compareExternalForms(a, c) <= 0,
                                written(a) + " <= " + written(b) + " <= " + written(c)
                                        + " but not " + written(a) + " <= " + written(c));
                    }
                }
            }
        }
    }

    // === sorting ===

    @Test
    @SuppressWarnings("unchecked")   // sortedArray answers Object; over a list it is the list back
    void sortedArrayPutsTheMembersInOrderWhicheverOrderTheyArrivedIn() {
        List<@Nullable Object> members = new ArrayList<>(CORPUS);
        List<@Nullable Object> forwards = (List<@Nullable Object>) Representations.sortedArray(members);
        List<@Nullable Object> reversed = new ArrayList<>(members);
        java.util.Collections.reverse(reversed);

        assertEquals(written(forwards), written(Representations.sortedArray(reversed)));
        assertTrue(isAscending(forwards), "not ascending: " + written(forwards));
    }

    @Test
    void sortedArrayIsIdempotent() {
        Object once = Representations.sortedArray(new ArrayList<>(CORPUS));
        assertEquals(written(once), written(Representations.sortedArray(once)));
    }

    @Test
    void sortedObjectPutsTheMembersInKeyOrder() {
        Object sorted = Representations.sortedObject(object("b", 2L, "a", 1L, "c", 3L));
        assertEquals(List.of("a", "b", "c"), new ArrayList<>(((Map<?, ?>) sorted).keySet()));
    }

    @Test
    void sortedObjectIsIdempotent() {
        Object once = Representations.sortedObject(object("b", 2L, "a", 1L));
        assertEquals(written(once), written(Representations.sortedObject(once)));
    }

    @Test
    void sortedObjectMovesItsOwnMembersAndNotWhatTheyHold() {
        Object sorted = Representations.sortedObject(object("b", List.of(3L, 1L, 2L), "a", 1L));
        assertEquals(List.of(3L, 1L, 2L), ((Map<?, ?>) sorted).get("b"));
    }

    // === the domain is closed ===

    @Test
    void aValueNoEncoderWritesIsRefusedRatherThanOrderedSomehow() {
        assertThrows(IllegalStateException.class,
                () -> Representations.compareExternalForms(1, 2));            // an Integer, not a Long
        assertThrows(IllegalStateException.class,
                () -> Representations.compareExternalForms(LocalDate.EPOCH, LocalDate.EPOCH));
        assertThrows(IllegalStateException.class,
                () -> Representations.compareExternalForms(new Object(), new Object()));
    }

    @Test
    void askingWhetherTwoAreWrittenTheSameRefusesWhatComparingThemRefuses() {
        assertThrows(IllegalStateException.class,
                () -> Representations.representationEquals(LocalDate.EPOCH, LocalDate.EPOCH));
        // including a value asked about against itself: a shortcut taken before the value is
        // recognised would answer for a carrier the comparison refuses, and the two would disagree
        Object foreign = new Object();
        assertThrows(IllegalStateException.class,
                () -> Representations.representationEquals(foreign, foreign));
    }

    @Test
    void askingWhetherTwoAreWrittenTheSameLooksInsideEvenTheSameContainerTwice() {
        // A container whose own carrier is fine and whose members are not: being handed the same
        // instance on both sides is not a reason to stop looking, or the two entry points would
        // answer over different domains.
        Object foreign = new Object();
        List<Object> array = List.of(foreign);
        assertThrows(IllegalStateException.class,
                () -> Representations.representationEquals(array, array));
        Map<String, Object> object = Map.of("x", foreign);
        assertThrows(IllegalStateException.class,
                () -> Representations.representationEquals(object, object));
    }

    @Test
    void askingWhetherTwoAreWrittenTheSameRefusesAKeyNoBoundaryObjectCanHave() {
        assertThrows(IllegalStateException.class,
                () -> Representations.representationEquals(Map.of(1L, "a"), Map.of(1L, "a")));
    }

    @Test
    void sortingRefusesWhatIsNotTheCollectionItSorts() {
        // The same refusal the comparison gives, rather than a ClassCastException from a cast that
        // happened to be where the mistake landed.
        assertThrows(IllegalStateException.class, () -> Representations.sortedArray(object("a", 1L)));
        assertThrows(IllegalStateException.class, () -> Representations.sortedObject(List.of(1L)));
        assertThrows(IllegalStateException.class, () -> Representations.sortedArray("not an array"));
        assertThrows(IllegalStateException.class, () -> Representations.sortedObject(null));
    }

    @Test
    void aRefusedValueIsRefusedWhereverItSits() {
        assertThrows(IllegalStateException.class,
                () -> Representations.compareExternalForms(List.of(1), List.of(2)));
        assertThrows(IllegalStateException.class,
                () -> Representations.compareExternalForms(object("a", 1), object("a", 2)));
    }

    // === helpers ===

    private interface Pair {
        void check(@Nullable Object a, @Nullable Object b);
    }

    private static void forEachPair(Pair check) {
        for (@Nullable Object a : CORPUS) {
            for (@Nullable Object b : CORPUS) {
                check.check(a, b);
            }
        }
    }

    private static boolean isAscending(List<@Nullable Object> xs) {
        for (int i = 0; i < xs.size() - 1; i++) {
            if (Representations.compareExternalForms(xs.get(i), xs.get(i + 1)) > 0) {
                return false;
            }
        }
        return true;
    }

    private static Map<String, Object> object(Object... keysAndValues) {
        Map<String, Object> m = new LinkedHashMap<>();
        for (int i = 0; i < keysAndValues.length; i += 2) {
            m.put((String) keysAndValues[i], keysAndValues[i + 1]);
        }
        return m;
    }

    /**
     * The oracle: the JSON an encoder writes for this form, with an object's members in key order
     * because their order is not part of what the object is. It is written here rather than asked of
     * {@link Representations} so that the law above is checked against something else.
     */
    private static String written(@Nullable Object v) {
        return switch (v) {
            case null -> "null";
            case Boolean b -> b.toString();
            case Long l -> l.toString();
            case BigDecimal d -> d.toString();      // what Jackson writes, exponent and all
            case String s -> "\"" + s + "\"";
            case List<?> xs -> {
                StringBuilder sb = new StringBuilder("[");
                for (int i = 0; i < xs.size(); i++) {
                    sb.append(i == 0 ? "" : ",").append(written(xs.get(i)));
                }
                yield sb.append("]").toString();
            }
            case Map<?, ?> m -> {
                StringBuilder sb = new StringBuilder("{");
                boolean first = true;
                List<String> keys = new ArrayList<>();
                m.keySet().forEach(k -> keys.add((String) k));
                keys.sort(null);
                for (String k : keys) {
                    sb.append(first ? "" : ",").append(written(k)).append(":").append(written(m.get(k)));
                    first = false;
                }
                yield sb.append("}").toString();
            }
            default -> throw new AssertionError("not an external form: " + v.getClass());
        };
    }
}
