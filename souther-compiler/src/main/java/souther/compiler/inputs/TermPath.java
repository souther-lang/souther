package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;

/**
 * A parameter-rooted coordinate: a parameter, and the steps taken from it.
 *
 * <p>It says where, and not what the location belongs to. An input reading writes its positions down
 * this way and so does a plan for building a value, and those are not one set of positions — what a
 * path is about is owned by whatever holds it ({@link Position}, {@code ConstructionPlan.Node}) and
 * is not readable off the coordinate. Read off it, a position of one would be looked up in the
 * other, which is the thing that has to stay impossible.
 *
 * <p>One coordinate for both, and not because they happen to spell alike. A class fixes an input
 * position, and the value that goes there is chosen at a position of the plan; the two meet by being
 * written the same way, so a second type would put a conversion exactly where the meeting is — and
 * the meeting is the protocol. Spelled the way {@code InvariantChecker} spells the same location for
 * that same reason: a partition derived from a parameter's type and a threshold read off a
 * {@code guard} are about one location or they are not, and if the two spellings disagree the same
 * position becomes two axes, one of which no row ever covers.
 *
 * <p><b>A coordinate, and nothing about how many values stand at one.</b> A {@link Step.Element}
 * says the position is inside the sequence above it; it does not say some element, or every element,
 * or one in particular. How many elements of a list a class has to hold is a property of what is
 * owed there and of the row that answers it, and putting it here would make two paths out of one
 * location — after which a rule written about the location and a row walked to it would no longer
 * meet, which is the whole of what one coordinate is for.
 *
 * <p>Steps are fields and elements and nothing else. That a newtype contributes no step is not this
 * type's rule and nothing here enforces it — whoever reads a structure takes its steps from what
 * {@link StructuralDescent} answers with, off a shape {@code TypeView} has already taken the worn
 * names off. So {@code data Amount = Int} is one location whether it is written {@code request.cost}
 * or {@code request.cost.value}, and a path ends at the newtype itself.
 */
public record TermPath(String head, List<Step> steps) {

    /** One step from a position to a position inside it. */
    public sealed interface Step {

        /** The field of a record. */
        record Field(String name) implements Step {

            @Override
            public String toString() {
                return name;
            }
        }

        /**
         * Inside the sequence the path has reached so far.
         *
         * <p>Which element is not something a coordinate can say, and not something it is short of
         * saying: a list holds as many as it holds, and they are one position because one rule is
         * written about them. What a class here means, and how many elements a row has to put in
         * one, are settled where the class and the row are and not here.
         */
        record Element() implements Step {

            @Override
            public String toString() {
                return "[*]";
            }
        }
    }

    public TermPath {
        steps = List.copyOf(steps);
    }

    public static TermPath of(String head) {
        return new TermPath(head, List.of());
    }

    /** The same path, one field further in. */
    public TermPath then(String field) {
        return append(new Step.Field(field));
    }

    /** The same path, inside the sequence it has reached. */
    public TermPath element() {
        return append(new Step.Element());
    }

    private TermPath append(Step step) {
        List<Step> longer = new ArrayList<>(steps);
        longer.add(step);
        return new TermPath(head, longer);
    }

    public int depth() {
        return steps.size();
    }

    /** Whether any step of this reaches inside a sequence. */
    public boolean insideASequence() {
        for (Step step : steps) {
            if (step instanceof Step.Element) {
                return true;
            }
        }
        return false;
    }

    /**
     * The sequence this position is inside, or this path where it is inside none.
     *
     * <p>Up to the first element step, which is the container a clause of the value can name — what
     * is written about what a list holds is written about the list. A position two sequences deep
     * answers with the outer one, since that is where the naming stops either way.
     */
    public TermPath containingSequence() {
        for (int i = 0; i < steps.size(); i++) {
            if (steps.get(i) instanceof Step.Element) {
                return new TermPath(head, steps.subList(0, i));
            }
        }
        return this;
    }

    /**
     * The dotted field name the clauses of a value name this position by, or null where no clause
     * can name it.
     *
     * <p>Null, and not the empty string, and not the fields with the element steps dropped. The
     * clauses of a record relate the fields of that record, and a position inside a sequence is not
     * one of them — {@code items.charge} is a field of what a list holds, and no clause of the
     * record holding the list is written at that name. Joined without the element step it would be
     * looked up as a field of the record itself, which is either nothing or, on the day a record has
     * a field spelled that way, another position's rules.
     *
     * <p>What does state a relation over the elements of a container is read as a quantifier over
     * the clause (spec §invariant-discharge-quantified) and is not one of these keys. So null says
     * this reading has nothing to say about the position, and not that nothing does.
     */
    public String fieldKey() {
        if (insideASequence()) {
            return null;
        }
        StringBuilder out = new StringBuilder();
        for (Step step : steps) {
            if (!out.isEmpty()) {
                out.append('.');
            }
            out.append(step);
        }
        return out.toString();
    }

    @Override
    public String toString() {
        StringBuilder out = new StringBuilder(head);
        for (Step step : steps) {
            if (step instanceof Step.Element) {
                out.append(step);
            } else {
                out.append('.').append(step);
            }
        }
        return out.toString();
    }
}
