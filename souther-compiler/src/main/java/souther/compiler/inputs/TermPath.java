package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A parameter-rooted location: a parameter, and the steps taken from it.
 *
 * <p>It says where, and not what the location belongs to. An input reading writes its positions down
 * this way and so does a plan for building a value, and those are not one set of positions — what a
 * path is about is owned by whatever holds it ({@link Position}, {@code ConstructionPlan.Node}) and
 * is not readable off the path. Read off it, a position of one would be looked up in the
 * other, which is the thing that has to stay impossible.
 *
 * <p>One spelling for both, and not because they happen to write alike. A class fixes an input
 * position, and the value that goes there is chosen at a position of the plan; the two meet by being
 * written the same way, so a second type would put a conversion exactly where the meeting is — and
 * the meeting is the protocol. Spelled the way {@code InvariantChecker} spells the same location for
 * that same reason: a partition derived from a parameter's type and a threshold read off a
 * {@code guard} are about one location or they are not, and if the two spellings disagree the same
 * position becomes two axes, one of which no row ever covers.
 *
 * <p><b>Two kinds of step, and they are not the same kind of thing.</b> A field and an element go
 * somewhere: what is at the end of one is inside what is at the start of it. A
 * {@link Step.Refine} goes nowhere — it narrows which values may stand at the position it is taken
 * at, and the value at the end of it is the value at the start of it. So a refinement takes no
 * level of the structure, reaches no field of a record it is under, and states a requirement about
 * the value rather than a place in it ({@link #requirements}).
 *
 * <p><b>A location, and nothing about how many values stand at one.</b> A {@link Step.Element}
 * says the position is inside the sequence above it; it does not say some element, or every element,
 * or one in particular. How many elements of a list a class has to hold is a property of what is
 * owed there and of the row that answers it, and putting it here would make two paths out of one
 * location — after which a rule written about the location and a row walked to it would no longer
 * meet, which is the whole of what one spelling is for.
 *
 * <p>Steps are fields, elements and refinements, and nothing else. That a newtype contributes no
 * step is not this type's rule and nothing here enforces it — whoever reads a structure takes its
 * steps from whichever question about a shape it is asking, off a shape {@code TypeView} has already
 * taken the worn names off. So {@code data Amount = Int} is one location whether it is written
 * {@code request.cost} or {@code request.cost.value}, and a path ends at the newtype itself.
 */
public record TermPath(String head, List<Step> steps) {

    /** One step of a path: two that go somewhere, and one that stays and narrows. */
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
         * <p>Which element is not something a path can say, and not something it is short of
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

        /**
         * The same position, with which values may stand at it narrowed.
         *
         * <p>Not a place inside the value. {@code query@GlobalQuery} is the value {@code query} is,
         * read as the case it turned out to be, and {@code query@GlobalQuery.tag} is a field of
         * that case at the same remove from the parameter as a field of a record parameter is. What
         * it adds is a requirement, and a row whose value does not meet it stands nowhere below it
         * rather than being a row nothing could read.
         */
        record Refine(Refinement refinement) implements Step {

            @Override
            public String toString() {
                return "@" + refinement.spelled();
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

    /** The same position, narrowed to the values {@code refinement} leaves. */
    public TermPath refine(Refinement refinement) {
        return append(new Step.Refine(refinement));
    }

    private TermPath append(Step step) {
        List<Step> longer = new ArrayList<>(steps);
        longer.add(step);
        return new TermPath(head, longer);
    }

    /**
     * What has to be true of the parameter for this position to exist in it.
     *
     * <p>One entry per refinement step, keyed by the position it was taken at — so a position two
     * refinements deep says both, and each is about the position that had to be narrowed rather
     * than about this one. Read here and nowhere else: every reader that decides whether two
     * positions or two classes can be in one row asks {@link Requirements#merge}, and none of them
     * keeps an account of its own.
     */
    public Requirements requirements() {
        Map<TermPath, Refinement> out = new LinkedHashMap<>();
        TermPath at = TermPath.of(head);
        for (Step step : steps) {
            if (step instanceof Step.Refine refine) {
                out.put(at, refine.refinement());
            }
            at = at.append(step);
        }
        return new Requirements(out);
    }

    /**
     * Whether this path's last step narrows the position it reaches.
     *
     * <p>The last step and not any of them: what is asked is whether <em>this</em> position is a
     * narrowing of the one above it, which is what says a caller asked something of it. A field of a
     * case is not one — the narrowing is at the case, which is a position of its own, and a caller
     * wanting to know whether this stands under one asks {@link #requirements}.
     */
    public boolean narrowsWhatItReaches() {
        return !steps.isEmpty() && steps.get(steps.size() - 1) instanceof Step.Refine;
    }

    /** Whether any step of this reaches inside a sequence. */
    public boolean insideASequence() {
        for (Step step : steps) {
            if (reachesInsideASequence(step)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether {@code step} goes inside a collection.
     *
     * <p>Exhaustive over {@link Step}, with no {@code default}, and the one place the question is
     * decided. Three readers ask it — whether this position is inside one at all, which one a clause
     * can name, and which ones have to hold a value for it to exist — and a step added later would
     * have joined whichever side each reader's condition happened to leave it on.
     */
    private static boolean reachesInsideASequence(Step step) {
        return switch (step) {
            case Step.Element _ -> true;
            // A field goes into the value and a narrowing stays at it. Neither is a container's
            // contents, so neither puts the position inside one.
            case Step.Field _, Step.Refine _ -> false;
        };
    }

    /**
     * Whether {@code other} is this path or a path below it.
     *
     * <p>Asked of the steps and never of how they are written. A rendering runs the steps together
     * with whatever each wears, so a test on the text has to name every separator a step can have —
     * and a position one collection or one refinement further in follows its container with no dot.
     */
    public boolean isAtOrUnder(TermPath other) {
        if (!head.equals(other.head) || steps.size() < other.steps.size()) {
            return false;
        }
        return steps.subList(0, other.steps.size()).equals(other.steps);
    }

    /**
     * The dotted field name the clauses of the value at {@code root} name this position by, or null
     * where none of them can name it.
     *
     * <p>{@link #fieldKey} asked of a value that is not the parameter. The rules of a
     * {@code GlobalQuery} are written about {@code tag} and the position is
     * {@code query@GlobalQuery.tag}: the translation belongs to whoever knows which value's rules
     * are being read, and putting it in {@link #fieldKey} would make this path know that too.
     *
     * <p>Null for a position under no such value as readily as for one no clause can name. A
     * reading of one value has nothing to say about a position in another, and answering with a
     * name would be that value's rules read at somebody else's position.
     */
    public String fieldKeyUnder(TermPath root) {
        List<Step> below = below(root);
        if (below == null) {
            return null;
        }
        for (Step step : below) {
            switch (step) {
                case Step.Field _ -> { }
                case Step.Element _, Step.Refine _ -> {
                    return null;
                }
            }
        }
        return spelled(below);
    }

    /**
     * The steps below {@code root} written out, or null where this is not under it.
     *
     * <p>{@link #stepsSpelled} asked of a value that is not the parameter, and what a table keyed by
     * such names looks a position up by. {@link #fieldKeyUnder} is this where a clause of that value
     * could name the position and null where none can.
     */
    public String stepsSpelledUnder(TermPath root) {
        List<Step> below = below(root);
        return below == null ? null : spelled(below);
    }

    /** The steps of this below {@code root}, or null where this is not under it. */
    private List<Step> below(TermPath root) {
        return isAtOrUnder(root) ? steps.subList(root.steps.size(), steps.size()) : null;
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
            if (reachesInsideASequence(steps.get(i))) {
                return new TermPath(head, steps.subList(0, i));
            }
        }
        return this;
    }

    /**
     * Every sequence this position stands inside, outermost first.
     *
     * <p>One per element step. A position two sequences deep stands inside both, and a value stands
     * at it only where each of them holds something — so a reader asking what has to hold a value
     * for this one to exist is owed all of them. {@link #containingSequence} answers with the first
     * and is asked the other question: which container a clause of the value can name.
     */
    public List<TermPath> sequencesContainingIt() {
        List<TermPath> out = new ArrayList<>();
        for (int i = 0; i < steps.size(); i++) {
            if (reachesInsideASequence(steps.get(i))) {
                out.add(new TermPath(head, steps.subList(0, i)));
            }
        }
        return List.copyOf(out);
    }

    /**
     * The dotted field name the clauses of a value name this position by, or null where no clause
     * of the value this is rooted at can name it.
     *
     * <p>Null for two unlike reasons, and both of them are the same shape of answer. The clauses of
     * a record relate the fields of that record, and a position inside a sequence is not one of
     * them — {@code items.charge} is a field of what a list holds, and no clause of the record
     * holding the list is written at that name. And a clause is not written across a refinement
     * either: what a {@code GlobalQuery} says about its {@code tag} is written in
     * {@code GlobalQuery}, not in the sum, so a reader with those rules in hand asks
     * {@link #fieldKeyUnder} the case rather than this.
     *
     * <p>Joined without those steps the name would be looked up as a field of the value itself,
     * which is either nothing or, on the day such a field exists, another position's rules.
     *
     * <p>What does state a relation over the elements of a container is read as a quantifier over
     * the clause (spec §invariant-discharge-quantified) and is not one of these keys. So null says
     * this reading has nothing to say about the position, and not that nothing does.
     */
    public String fieldKey() {
        return fieldKeyUnder(TermPath.of(head));
    }

    /**
     * The steps written out, with the parameter left off.
     *
     * <p>A name for the location under whatever holds it, which is what a table keyed by such names
     * looks a position up by. Where a step reaches inside a sequence or narrows the position the
     * name still spells it, so two positions never come to one name — and no clause of a value is
     * written at such a name, so a lookup finds nothing, which is the true answer and not a
     * collision.
     *
     * <p>{@link #fieldKey} is this where a clause of the value could name the position and null
     * where none can. A caller deciding what a clause says wants that one; a caller needing a name
     * for every position wants this.
     */
    public String stepsSpelled() {
        return spelled(steps);
    }

    private static String spelled(List<Step> steps) {
        StringBuilder out = new StringBuilder();
        for (Step step : steps) {
            spell(out, step);
        }
        return out.toString();
    }

    /**
     * One step, as it is written after what came before it.
     *
     * <p>Exhaustive over {@link Step}, with no {@code default}, and the one place a step's
     * separator is decided. A step added later stops this compiling rather than arriving in a
     * report under a dot that says it is a field.
     */
    private static void spell(StringBuilder out, Step step) {
        switch (step) {
            case Step.Field field -> {
                if (!out.isEmpty()) {
                    out.append('.');
                }
                out.append(field);
            }
            // Neither wears a separator: what a list holds follows the list, and a narrowing of a
            // position follows the position, and a dot before either would read as a field of it.
            case Step.Element _, Step.Refine _ -> out.append(step);
        }
    }

    @Override
    public String toString() {
        StringBuilder out = new StringBuilder(head);
        for (Step step : steps) {
            spell(out, step);
        }
        return out.toString();
    }
}
