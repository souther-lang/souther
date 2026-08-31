package souther.compiler.check;

/**
 * One question a rule raises, and what it is about.
 *
 * <p><b>The question and its subject are one thing and not two beside each other.</b> The
 * obligations do not share a subject — what values may stand somewhere is about a name, where a
 * line falls is about a number of one — and a rule bounding a {@code String} on its length raises
 * both, the values being the string's and the line being on the length. Which subject an obligation
 * has does not vary, so it is the arm. Carried as an obligation beside a subject, the pair was a
 * product every combination of which was a value of this type, and the reader that would have met
 * one nothing raises fenced it off with a throw.
 *
 * <p>Which arm a clause raises follows from the clause and is settled where the question is raised,
 * so no reader downstream chooses between a path and a number.
 *
 * <p><b>Two arms, because two are what anything raises.</b> The place a comparison of two moving
 * things draws was a third and nothing ever built one. {@link CoverageObligation} says why and
 * always did: such a line owes the rows either side of it by having been read, so no demand about
 * it is ever outstanding, and what it owes lives where the partition's geometry does. An arm
 * nothing raises is a question every model answers by nobody having asked it, and a completeness
 * counted over such a set says more than it knows.
 */
public sealed interface Owed {

    /**
     * Which values may stand at a name.
     *
     * <p>The name and never a number at it. What a rule about the length of a string admits is
     * a set of strings; the length is where its line falls, which is the question below.
     *
     * @param path what the value's own rules call the place, {@link RuleKey#THE_VALUE} for the
     *             value itself
     */
    record AdmittedValues(RuleKey path) implements Owed {

        public AdmittedValues {
            if (path == null) {
                throw new IllegalArgumentException("a subject is at a name of the value");
            }
        }

        @Override
        public String toString() {
            // The value itself is at no name, which reads as nothing at all where it is printed.
            return path.isTheValueItself() ? "the value" : path.toString();
        }
    }

    /**
     * Where a line falls on one number at one name.
     *
     * <p>The number itself, which is the value at the name or what an operation answers of it.
     * Two operations over one name are two of these, and that is the whole reason the coordinate is
     * carried rather than a flag saying that a number was taken: told apart by the flag, a rule
     * about one operation's number was filed at another's, and every reader that wanted the name
     * reached past the question to whatever stood beside it.
     */
    record Boundary(FieldDomains.Coordinate on) implements Owed {

        public Boundary {
            if (on == null) {
                throw new IllegalArgumentException("a line falls on some number");
            }
        }

        @Override
        public String toString() {
            return on.toString();
        }
    }

    /**
     * What this question asks, which is the arm and is derived rather than carried.
     *
     * <p>Stored beside the subject, the two could disagree — and one of the two combinations that
     * disagreement makes was a value nothing produced and one reader threw over.
     */
    default CoverageObligation obligation() {
        return switch (this) {
            case AdmittedValues _ -> CoverageObligation.ADMITTED_VALUES;
            case Boundary _ -> CoverageObligation.BOUNDARY;
        };
    }
}
