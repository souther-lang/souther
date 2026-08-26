package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;

/**
 * Where in an answer something sits, as the steps of the answer's own shape.
 *
 * <p>The shape and not the heap. A walk of two answers, or of one, gets from an answer to an object
 * by taking a member of it, an element of a collection, a key or a value of a map, or what an
 * absence holds — and those are the steps, kept as what they are. Written as text on the way, two of
 * them come out the same: a member called {@code value} and the value side of a map are both
 * {@code .value}, and a reader of a path cannot tell which happened. Kept as steps, they are two
 * things and are rendered as two.
 *
 * <p>What is one step here is one step because nothing tells the two apart. A record's component and
 * a class's field are reached the same way and are written the same way, and an array's element and a
 * list's are too — a pair of arms nothing can distinguish is a distinction a reader would go looking
 * for and never find.
 *
 * <p><b>An occurrence and not an object.</b> One object under an answer is held by however many
 * paths hold it, and each of those is a place the answer exposes it. So a locus says which way down
 * was taken, and the same object reached twice is two loci rather than one — which is what lets a
 * register of what an answer holds be a register of places rather than of classes.
 *
 * <p>What is not here is a step into a case of a sum. Nothing walks one: a case is what an object's
 * class is, and the walk reaches it by being at the object. A step for it would be a word no walk
 * writes.
 */
record Locus(List<Locus.Step> steps) {

    /**
     * One place in one answer, as both detectors name one and the register is keyed by.
     *
     * <p>Kept as what it is until a failure is written. Flattened to text where it is compared, two
     * places whose rendering happens to agree are one line in a register that is meant to hold one
     * line per place — and which two those are moves with how a step is spelled rather than with
     * anything about the answers.
     *
     * @param question the key that asks it, by class, or {@code *} for a place every answer has
     * @param offender the class of the thing there, or the array type
     */
    record Place(String question, Locus at, String offender) implements Comparable<Place> {

        @Override
        public int compareTo(Place other) {
            return toString().compareTo(other.toString());
        }

        @Override
        public String toString() {
            return question + at + " " + offender;
        }
    }

    /** This place in the answer {@code question} asks, holding {@code offender}. */
    Place of(String question, String offender) {
        return new Place(questionOf(question), this, offender);
    }

    /** One way down from a thing an answer holds to something it holds. */
    sealed interface Step {

        /**
         * A member of the thing above, by what declares it and the name it is declared under.
         *
         * <p>The declaring type and not only the name. Two arms of one sum can each hold a thing of
         * one class under a component of one name, and a walk that reached them through a collection
         * writes the same steps for both — so one line would stand for two places, one of them would
         * be fixed, and the line would stay because the other still holds.
         *
         * <p><b>{@code owner} is what the type is called and not what a reader calls it.</b> Two
         * classes of one simple name are two types, so a step that kept the short name would put
         * them back together — the collision this exists to prevent, one level in. What is shown is
         * shortened where it is written out, which is a reader's business and not this one's.
         */
        record Member(String owner, String name) implements Step {

            /** What to call it where somebody is reading. */
            String shown() {
                return owner.substring(Math.max(owner.lastIndexOf('.'), owner.lastIndexOf('$')) + 1);
            }
        }

        /** An element of an array or of a collection. Which one is not kept: an answer is not more
         *  or less exposed at the third element than at the first, and the index would put the
         *  order of a walk into a register. */
        record Element() implements Step {}

        /** The key side of a map's entry. */
        record MapKey() implements Step {}

        /** The value side of one. */
        record MapValue() implements Step {}

        /** What an absence holds, where it holds something. */
        record Present() implements Step {}
    }

    /** The answer itself. */
    static final Locus ROOT = new Locus(List.of());

    /**
     * What every answer holds beside what it came to: the reports the compile made getting there.
     *
     * <p>Read off the record rather than written out, so that renaming the component moves this with
     * it instead of leaving a string nobody notices is stale.
     */
    private static final Step.Member WHAT_WAS_SAID = new Step.Member(
            Answer.class.getName(), Answer.class.getRecordComponents()[1].getName());

    /**
     * Whether this is a place every answer has, rather than a place in one answer's value.
     *
     * <p>An answer is what a question came to and what was said getting there. The first of those is
     * a different shape per question, so where something sits inside it is a place in that question's
     * answer. The second is the same shape in every answer there is — so something sitting in there
     * sits in the same place whichever question happens to have said anything, and a register that
     * named the question would hold one line per question that ever spoke, all of them about one
     * thing, and each of them an artifact of which model a scenario compiled.
     */
    boolean inEveryAnswer() {
        return !steps.isEmpty() && WHAT_WAS_SAID.equals(steps.getFirst());
    }

    /** Which answer this is in, or {@code *} where it is a place every answer has. */
    String questionOf(String question) {
        return inEveryAnswer() ? "*" : question;
    }



    Locus {
        steps = List.copyOf(steps);
    }

    /** The same locus with one more step at the end. */
    Locus then(Step step) {
        List<Step> out = new ArrayList<>(steps);
        out.add(step);
        return new Locus(out);
    }

    /** The member {@code owner} declares under {@code name}. */
    Locus thenMember(Class<?> owner, String name) {
        return then(new Step.Member(owner.getName(), name));
    }

    /**
     * {@code inner} read as a locus under this one.
     *
     * <p>What a walk that remembers what it found under a pair needs. What was found there is kept
     * relative to it, and every path that reaches the pair again writes those out again from where it
     * stands — so the steps are joined rather than a rendered path being cut at a length.
     */
    Locus followedBy(Locus inner) {
        List<Step> out = new ArrayList<>(steps);
        out.addAll(inner.steps());
        return new Locus(out);
    }

    /**
     * This locus as one string.
     *
     * <p>The brace forms are what keep a map apart from a member. A record with a component called
     * {@code value} and the value side of a map are different steps and read differently here, which
     * is the whole reason the steps are kept.
     */
    String rendered() {
        StringBuilder out = new StringBuilder();
        for (Step step : steps) {
            out.append(switch (step) {
                case Step.Member member -> "." + member.shown() + "#" + member.name();
                case Step.Element _ -> "[]";
                case Step.MapKey _ -> "{key}";
                case Step.MapValue _ -> "{value}";
                case Step.Present _ -> "?";
            });
        }
        return out.toString();
    }

    @Override
    public String toString() {
        return rendered();
    }
}
