package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;

/**
 * Where in a declared answer a type stands, as the steps the declarations take to reach it.
 *
 * <p>The declarations and not the heap. A walk of types gets from what a question answers with to a
 * type under it by taking a member of it, an argument of a container, or an arm of a sum — and those
 * are the steps, kept as what they are.
 *
 * <p><b>An arm is a step here and is not one in {@link Locus}.</b> A walk of objects reaches a case
 * of a sum by being at the object, and has nothing to write down about the choice; a walk of types
 * has to take every arm, and which one it is under is the difference between two places that
 * otherwise read alike. So the two paths are two things rather than one with a step nobody writes.
 */
record TypePath(List<TypePath.Step> steps) {

    static final TypePath ROOT = new TypePath(List.of());

    /**
     * One place in one declared answer.
     *
     * @param question the key that declares it, by class
     * @param offender the type there, by what it is called
     */
    record Place(String question, TypePath at, String offender) {

        /** This place as one line, for somebody reading a failure. */
        String asText() {
            return question + at.asText() + " " + offender;
        }
    }

    /** One way down from a declared type to a type under it. */
    sealed interface Step {

        /** A member of the type above, by what declares it and the name it is declared under. */
        record Member(String owner, String name) implements Step {}

        /** An argument the declaration wrote, by which one it is: what a list holds is its only
         *  one, and what a map holds is its second. */
        record Argument(String named) implements Step {}

        /** One arm of a sum, which a walk of types takes all of. */
        record Arm(String named) implements Step {}
    }

    TypePath then(Step step) {
        List<Step> out = new ArrayList<>(steps);
        out.add(step);
        return new TypePath(List.copyOf(out));
    }

    TypePath thenMember(Class<?> owner, String name) {
        return then(new Step.Member(owner.getTypeName(), name));
    }

    /** This path as text, with each kind of step spelled as itself. */
    String asText() {
        StringBuilder out = new StringBuilder();
        for (Step step : steps) {
            switch (step) {
                case Step.Member(String owner, String name) ->
                        out.append('.').append(shortly(owner)).append('#').append(name);
                case Step.Argument(String named) -> out.append('<').append(named).append('>');
                case Step.Arm(String named) -> out.append('|').append(shortly(named));
            }
        }
        return out.toString();
    }

    /** A type by the last of what it is called, which is what a reader of a failure follows. */
    private static String shortly(String named) {
        int at = Math.max(named.lastIndexOf('.'), named.lastIndexOf('$'));
        return at < 0 ? named : named.substring(at + 1);
    }

    /** This place in the answer {@code question} declares, holding {@code offender}. */
    Place of(String question, String offender) {
        return new Place(question, this, offender);
    }
}
