package souther.compiler.reading;

import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.coverage.ForkOccurrence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

/**
 * One decision of a body coming out one way, said in terms of the input it is about.
 *
 * <p>Not the arm. A condition stops as soon as it is settled, so under {@code A && B} the arm taken
 * when the condition fails is reached both by a value that made {@code B} false and by one that
 * never evaluated {@code B} — an arm cannot say which comparison came out which way. What a row is
 * steered by is the comparison, so that is what is kept, on the id the comparison already has.
 */
public sealed interface Condition {

    /**
     * A case of a union the body matched on.
     *
     * @param name which case, as the model spells it
     */
    record Case(TermPath at, String name) implements Condition {

        @Override
        public String toString() {
            return at + "=" + name;
        }
    }

    /**
     * A comparison in the body coming out one way.
     *
     * <p><b>Said of the number it compares and not of the location that number is read from.</b>
     * Two numbers taken of one location — which hour of a time it is and which minute — are two
     * things to steer a row by and one path, so a reader given the path has to pick between them
     * and has nothing to pick with.
     *
     * @param at         which number, which is a location's own content or something taken of it
     * @param comparison which comparison, which is what tells one reading of one rule from another:
     *                   a comparison inside a non-recursive helper is read once per call of that
     *                   helper. The occurrence and not the number it is instrumented under — the
     *                   number is how a run is recorded and is no part of what this decision is
     * @param held       the way it came out
     */
    record Side(NumericTerm at, ComparisonOccurrence comparison, boolean held) implements Condition {

        @Override
        public String toString() {
            return at + (held ? " holds" : " fails") + " at " + comparison;
        }
    }

    /**
     * A fork coming out one way, where the reading could not say which input position it is about.
     *
     * <p>Still two outcomes and not one. What the position is decides whether a row can be steered
     * into this outcome; whether the outcomes are two is decided by the fork having two arms, and
     * running them together would report a factor the body has as one it does not.
     *
     * <p>Nothing can place one of these at a class of a position, so a group made of one is not a
     * group anything offers. That it is here at all is what says so: the walk found a decision it
     * could not name, and a reading that left it out instead would offer the group with one of the
     * ways it can be settled quietly missing.
     *
     * @param fork which fork, as the plan named it
     * @param part which arm of it
     */
    record Arm(ForkOccurrence fork, int part) implements Condition {

        @Override
        public String toString() {
            return fork + "/" + part;
        }
    }
}
