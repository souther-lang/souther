package souther.compiler.reading;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.core.Core;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.coverage.ArmOccurrence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ResolvedCase;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;

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

    /** The finalizer of a 32-bit murmur hash: every bit of the input moves every bit of the output. */
    static int mixed(int h) {
        int x = h;
        x ^= x >>> 16;
        x *= 0x85ebca6b;
        x ^= x >>> 13;
        x *= 0xc2b2ae35;
        x ^= x >>> 16;
        return x;
    }

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
         * The case {@code arm} is of the value at {@code at}.
         *
         * <p>The leaves the arm reaches and not the names it is written with. A case that is itself
         * a sum stands for the leaves under it, and those are what a value at the position is; read
         * by the written name, an arm for such a case admitted none of them.
         */
        public static Case of(TermPath at, Core.Case arm) {
            List<String> names = new ArrayList<>();
            for (ResolvedCase each : arm.pattern().cases()) {
                if (each.atoms().isEmpty()) {
                    names.add(each.name().name());
                } else {
                    each.atoms().forEach(atom -> names.add(atom.name()));
                }
            }
            return new Case(at, names);
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
     * @param visit    which of a run's visits to the comparison this is the decision on, where the
     *                 comparison stands in a closure applied to each element of a list written out:
     *                 the same construct is then one decision per application, about that
     *                 application's own number, and two of them coming out different ways is a row
     *                 doing two things. Which application a visit is, is the reading's to have
     *                 shown and is not said here. Empty where the comparison is visited once
     * @param held     the way it came out
     * @param line     what the comparison places on the number, where the other side is a value
     *                 the number's order writes; empty where it is another position or a value
     *                 this compiler does not place. Read off the same comparison as {@code at},
     *                 so it says nothing {@code statedAt} does not already decide
     */
    record Side(NumericTerm at, ConstructOccurrence statedAt, OptionalInt visit, boolean held,
                Optional<Line> line) implements Condition {

        public Side {
            Objects.requireNonNull(visit, "a comparison is decided on some visit, or on the one");
            Objects.requireNonNull(line, "a comparison places a line or says it places none");
        }

        /**
         * Where a comparison's line falls on the number it compares, and what it claims there.
         *
         * <p>What a reader needs to ask whether coming out one way is open to a value at all —
         * under one case of a sum, a number the cases share may be held where the comparison
         * never comes out the way a decision went.
         */
        public record Line(Place at, ComparisonClaim claim) {

            /** The relation a value stands in to the line where the comparison comes out
             *  {@code held}. */
            public Rel holding(boolean held) {
                return held ? claim.statedRelation() : claim.denied().statedRelation();
            }
        }

        /**
         * Spread over the whole of an int.
         *
         * <p>The decisions of one comparison in a closure applied to each element of a list differ
         * only in the visit and in the way it came out. Hashed as the fields are, those two enter
         * the hash linearly, and a set of such decisions — which hashes to the sum of its members —
         * then depends only on how many of them held: the combinations of a group fall into as many
         * buckets as there are counts, and a lookup among thousands of them compares deep values
         * against all the others in its bucket.
         */
        @Override
        public int hashCode() {
            return mixed(Objects.hash(at, statedAt, visit, held, line));
        }

        /** The same comparison coming out the other way. */
        @Override
        public boolean excludes(Condition other) {
            return other instanceof Side that && that.statedAt.equals(statedAt)
                    && that.visit.equals(visit) && that.held != held;
        }

        @Override
        public String toString() {
            return at + (held ? " holds" : " fails") + " at " + statedAt
                    + (visit.isPresent() ? " on visit " + visit.getAsInt() : "");
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
     * @param decidedBy the construct whose answer decides the fork, where what decides it is one
     *                  ({@link #decidingConstructOf}): what a reading that could name no subject
     *                  for the fork can still ask another reading about
     */
    record Arm(ArmOccurrence arm, Optional<ConstructOccurrence> decidedBy) implements Condition {

        public Arm {
            Objects.requireNonNull(arm, "an arm of some fork");
            Objects.requireNonNull(decidedBy, "decided by some construct, or by none said");
        }

        /**
         * The construct whose answer {@code decides} comes to, past the names bound on the way to
         * it: a comparison, a call, a fork. Empty where it ends at anything else.
         *
         * <p>Past the names because that is what an expansion leaves of a closure applied in an
         * operation's body: its parameter bound to what the operation handed it, around the body
         * the model wrote. The same answer for the closure as written, so the two readings of a
         * body meet at the construct the model wrote.
         */
        public static Optional<ConstructOccurrence> decidingConstructOf(Core decides) {
            Core at = Core.withoutStanding(decides);
            while (at instanceof Core.LetIn let) {
                at = Core.withoutStanding(let.body());
            }
            ConstructOccurrence construct = switch (at) {
                case Core.Binary binary -> binary.occurrence();
                case Core.Call call -> call.occurrence();
                case Core.PreservedCall call -> call.occurrence();
                case Core.If iff -> iff.occurrence();
                case Core.Match match -> match.occurrence();
                default -> null;
            };
            // A construct no author wrote is one place for every such construct, and so names none.
            return construct == null || !construct.isWritten() ? Optional.empty()
                    : Optional.of(construct);
        }

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
