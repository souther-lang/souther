package souther.compiler.partition;

import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CodePointClass;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;

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
        return counts.holding(this::holding);
    }

    @Override
    public PatternPlan stringsOutside() {
        return counts.holdingOtherwise(this::holding);
    }

    /** The strings no run gets to the relation with, which are those of the other counts: those
     *  holding fewer of the class than the least, and those holding more than the most. None
     *  where the strings of these counts are all of them. */
    List<PatternPlan> outside() {
        List<PatternPlan> out = new ArrayList<>();
        PatternPlan fewer = fewerThan();
        if (fewer != null) {
            out.add(fewer);
        }
        PatternPlan more = moreThan();
        if (more != null) {
            out.add(more);
        }
        return out;
    }

    /** The strings holding fewer than the least, or null where no string does. */
    PatternPlan fewerThan() {
        return counts.fewerThan(this::holding);
    }

    /** The strings holding more than the most, or null where no string does: only a string
     *  longer than the most holds more of the class than that. */
    PatternPlan moreThan() {
        return counts.moreThan(this::holding);
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
