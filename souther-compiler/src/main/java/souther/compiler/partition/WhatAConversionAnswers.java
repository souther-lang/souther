package souther.compiler.partition;

import net.unit8.notation199x.pattern.Meter;

import souther.compiler.regex.CodeMap;
import souther.compiler.regex.Language;
import souther.compiler.semantics.CaseMapping;

/**
 * What the strings of one side of a relation come to when a case conversion is done to them, as
 * far as it is shown, in two kinds of strings that are told apart by what may be done with them.
 *
 * <p>The values are strings that are all values held as written, so a string made from one is a
 * value as well: the strings inside it, or those that convert to it. They are the strings the
 * conversion is exactly a map on, converted ({@link CodeMap}), or the strings held as written of
 * the side itself where there is no conversion.
 *
 * <p>The strings left standing are the strings the conversion leaves as they stand
 * ({@link CaseMaps#answeredAsTheyStand}). A language holds sequences of code points, and these
 * include sequences that are no value, so what they say is only of a value: that it is among the
 * answers. Nothing is made from them: a string inside one is made from a sequence no value is, and
 * is not an answer's for that.
 *
 * <p>The two are joined only where a string is asked about as it stands, which is an equality
 * ({@link #forEquality}); a relation that makes strings from the answers asks
 * {@link #forDerivation}, which holds the values alone. The strings left standing are held
 * privately, so a caller cannot reach the sequences that are no value without saying it is asking
 * about an equality.
 */
final class WhatAConversionAnswers {

    private final Language values;
    /** The strings the conversion leaves as they stand, or null where there is no conversion or
     *  they are not worked out within the allowance. */
    private final Language standing;
    private final Language may;

    private WhatAConversionAnswers(Language values, Language standing, Language may) {
        this.values = values;
        this.standing = standing;
        this.may = may;
    }

    /**
     * What {@code through} comes to of the strings of {@code partner}, or null where the machines
     * for them are more than {@code meter} allows.
     */
    static WhatAConversionAnswers of(Language partner, CaseMapping through, Meter meter) {
        if (through.equals(CaseMapping.NONE)) {
            Language held = partner.heldAsWritten().language(meter);
            return held == null ? null : new WhatAConversionAnswers(held, null, partner);
        }
        CodeMap map = CaseMaps.of(through);
        Language exact = map.strings(meter);
        Language within = exact == null ? null : partner.and(exact, meter);
        Language outside = exact == null ? null : partner.and(exact.not(meter), meter);
        Language values = within == null ? null : map.answersTo(within, meter);
        Language left = outside == null || outside.isEmpty() ? null
                : CodeMap.stringsOf(map.leftAlone(), meter);
        Language may = values == null || outside == null ? null
                : left == null ? values : values.or(left, meter);
        if (may == null) {
            return null;
        }
        // Strings left as they stand are shown wherever the side holds them, so that failing to
        // work them out leaves what is shown without them and does not lose it.
        Language standing = CaseMaps.answeredAsTheyStand(through, partner, meter);
        return new WhatAConversionAnswers(values, standing, may);
    }

    /** The strings to make other strings from: values alone. */
    Language forDerivation() {
        return values;
    }

    /** The strings outside which no answer is, which hold the values. */
    Language may() {
        return may;
    }

    /** The strings an equality is shown at, and those outside which it is shown not to be. */
    Shown forEquality(Meter meter) {
        Language shown = standing == null ? null : values.or(standing, meter);
        Language mayBe = standing == null ? null : may.or(standing, meter);
        // What is shown is among what may be, so one of the two not worked out leaves both as
        // they were.
        return shown == null || mayBe == null ? new Shown(values, may) : new Shown(shown, mayBe);
    }

    /** The strings shown at, and the strings outside which an answer is not. */
    record Shown(Language canBe, Language mayBe) {
    }
}
