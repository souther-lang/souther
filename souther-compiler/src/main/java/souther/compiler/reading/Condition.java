package souther.compiler.reading;

import souther.compiler.types.ConstructOccurrence;
import souther.compiler.coverage.ArmOccurrence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.List;

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
     * Whether no run settles both this and {@code other}.
     *
     * <p>Asked of the condition and answered by what it means, so that a reader holding two of them
     * never compares how they are held. Two conditions that may both hold are no contradiction
     * however differently they are written, and a path read as contradicting itself is a path the
     * body has thrown away.
     */
    boolean excludes(Condition other);

    /**
     * That the value at a position is one of a set of cases of its union.
     *
     * <p>A set and held as one: the cases are kept once each and in the one order a set of them is
     * written in, so two arms admitting the same cases are the same condition whichever order they
     * name them in.
     *
     * @param names which cases, as the model spells them: the leaves of the union, and so several
     *              where the arm is written for several or for a case that is itself a union, since
     *              what the arm admits is each value it can be
     */
    record Case(TermPath at, List<String> names) implements Condition {

        public Case {
            names = names.stream().distinct().sorted().toList();
            if (names.isEmpty()) {
                throw new IllegalArgumentException("an arm at " + at + " answers for no case");
            }
        }

        /**
         * Whether the value can be in both sets, which is where they share a case. A value is one
         * case, so two sets with none in common are one way and another of the same decision.
         */
        @Override
        public boolean excludes(Condition other) {
            return other instanceof Case that && that.at.equals(at)
                    && Collections.disjoint(that.names, names);
        }

        /** The cases as one word, which is how a document and a person are shown them. */
        public String spelled() {
            return String.join("|", names);
        }

        @Override
        public String toString() {
            return at + "=" + spelled();
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
     * @param at       which number, which is a location's own content or something taken of it
     * @param statedAt which construct stated the comparison, in which place in the tree that runs —
     *                 a comparison the author wrote, or an application of an operation that means
     *                 one. What tells one decision from another, and what a rule's line is filed
     *                 under too. The materialisation and not the construct of the model it is one
     *                 of: an operation that evaluates a closure it was handed twice compares two
     *                 values, so the two coming out different ways is a row doing two things and not
     *                 a row contradicting itself. Read as one, a path the body has would be thrown
     *                 away.
     *                 <p>The occurrence and not the number it is instrumented under — the number is
     *                 how a run is recorded and is no part of what this decision is
     * @param held     the way it came out
     */
    record Side(NumericTerm at, ConstructOccurrence statedAt, boolean held) implements Condition {

        /** The same comparison coming out the other way. */
        @Override
        public boolean excludes(Condition other) {
            return other instanceof Side that && that.statedAt.equals(statedAt)
                    && that.held != held;
        }

        @Override
        public String toString() {
            return at + (held ? " holds" : " fails") + " at " + statedAt;
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
     * @param arm which arm of which fork. The fork as the tree that runs has it and not the number
     *            a plan handed its arms: an operation that applies the block it was handed twice
     *            settles the fork inside it twice, on values of its own, so the two are two
     *            decisions — and the number that told them apart was the walk's and not theirs
     */
    record Arm(ArmOccurrence arm) implements Condition {

        /** Another arm of the same fork. */
        @Override
        public boolean excludes(Condition other) {
            return other instanceof Arm that && that.arm.fork().equals(arm.fork())
                    && that.arm.part() != arm.part();
        }

        @Override
        public String toString() {
            return String.valueOf(arm);
        }
    }
}
