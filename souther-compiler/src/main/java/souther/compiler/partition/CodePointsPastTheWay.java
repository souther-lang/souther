package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.values.TextExtents;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * The strings that hold, of the code points of {@code counted}, a number {@code counts} allows.
 *
 * <p>A string holds that many exactly when it is written as stretches of the other code points
 * with one of the class between each two: the strings of {@code least} to {@code most} of the
 * class are {@code N*(C N*){least,most}}, with {@code C} the class and {@code N} the code points
 * not in it. The strings with fewer or more are the same with the other counts, so the two
 * partition every string.
 *
 * @param counted the code points counted
 * @param counts  the numbers of them a string holds
 */
record CodePointsPastTheWay(CodePointClass counted, LengthsPastTheWay.Lengths counts)
        implements StringsPastTheWay {

    CodePointsPastTheWay {
        if (counted == null || counts == null) {
            throw new IllegalArgumentException("some of the code points of a string are counted");
        }
    }

    @Override
    public boolean isEmpty() {
        return counts.isEmpty();
    }

    @Override
    public PatternPlan strings() {
        if (isEmpty() || counts.least().bitLength() >= Integer.SIZE - 1) {
            return null;
        }
        return PatternPlan.of(holding(counts.least().intValueExact(), ceiling()));
    }

    @Override
    public PatternPlan stringsOutside() {
        if (isEmpty()) {
            return null;
        }
        PatternPlan below = fewerThan();
        PatternPlan above = moreThan();
        if (counts.least().signum() > 0 && below == null) {
            return null;
        }
        return below == null ? above : above == null ? below : below.or(above);
    }

    /**
     * The strings no run gets to the relation with, as the numbers of the class they hold leave
     * them open.
     *
     * @param strings the strings
     * @param why     how few or how many of the class they hold
     */
    record Open(PatternPlan strings, BlockReason.CodePointsLeftOpen why) { }

    /** The strings of the other counts, each as it is left open: those holding fewer of the class
     *  than the least, and those holding more than the most. None where the strings of these
     *  counts are all of them. */
    List<Open> outside() {
        List<Open> out = new ArrayList<>();
        PatternPlan fewer = fewerThan();
        if (fewer != null) {
            out.add(new Open(fewer, new BlockReason.CodePointsLeftOpen(counted,
                    counts.least().longValueExact(), null)));
        }
        PatternPlan more = moreThan();
        if (more != null) {
            out.add(new Open(more, new BlockReason.CodePointsLeftOpen(counted, null,
                    counts.most().longValueExact())));
        }
        return out;
    }

    /** The strings holding fewer than the least, or null where no string does. */
    PatternPlan fewerThan() {
        if (isEmpty() || counts.least().signum() == 0
                || counts.least().bitLength() >= Integer.SIZE - 1) {
            return null;
        }
        return PatternPlan.of(holding(0, counts.least().intValueExact() - 1));
    }

    /** The strings holding more than the most, or null where no string does. */
    PatternPlan moreThan() {
        if (isEmpty() || !countsPastTheMost() || counts.most().bitLength() >= Integer.SIZE - 1) {
            return null;
        }
        return PatternPlan.of(holding(counts.most().intValueExact() + 1,
                PatternMeaning.Repeated.NO_CEILING));
    }

    /** Whether a string can hold more of the class than the most: only a string that is
     *  longer than that has. */
    private boolean countsPastTheMost() {
        return counts.most().compareTo(BigInteger.valueOf(TextExtents.LONGEST_STRING)) < 0;
    }

    private int ceiling() {
        return countsPastTheMost() && counts.most().bitLength() < Integer.SIZE - 1
                ? counts.most().intValueExact() : PatternMeaning.Repeated.NO_CEILING;
    }

    private PatternMeaning holding(int least, int most) {
        CodePoints in = counted.held();
        PatternMeaning others = new PatternMeaning.Repeated(
                new PatternMeaning.Symbols(in.not()), 0, PatternMeaning.Repeated.NO_CEILING);
        PatternMeaning one = new PatternMeaning.InTurn(
                List.of(new PatternMeaning.Symbols(in), others));
        return new PatternMeaning.InTurn(List.of(others,
                new PatternMeaning.Repeated(one, least, most)));
    }
}
