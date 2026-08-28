package souther.compiler.values;

import souther.compiler.regex.PatternSyntax;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which values one position admits, said as what it is rather than built as it is read.
 *
 * <p>The rules about a position are read one at a time and what they leave is one set, and those
 * two facts used to be the same walk: every conjunct met the last, so the set a position finally
 * admitted was a side effect of the order the clause put its parts in. Three things followed from
 * that and none of them was about the values. What was charged was what each step happened to
 * produce; which step was refused turned on which operands arrived together; and a refusal was
 * blamed on whatever rule was in hand when the allowance ran out.
 *
 * <p>So the reading says what the position admits and nothing else. What is here is a description —
 * the sets the rules name, met and joined the way the clause states them — and it is turned into a
 * {@link ValueSet} once, by something with an allowance to spend ({@link Sets}). Source order is
 * gone by then: two clauses that state the same thing in a different order are the same plan.
 *
 * <p><b>Normalised where it is made.</b> A meet of meets is one meet, {@link #ANY} met with
 * something is that something, a set stated twice is stated once, and two finite sets meet by
 * arithmetic that costs nothing. What is left after that is what actually has to be built, and
 * everything downstream — how it is planned, what it costs, whether it is refused — is a function
 * of it. A plan that kept the shape the author wrote would make the answer turn on the writing
 * again, one step further along.
 *
 * <p>{@link ValueSet} is not this and never becomes it. A set is exact, and what a reader asks of
 * one is answered by looking; this is what is asked for before there is a set to look at.
 */
public sealed interface AdmittedPlan {

    /** Every value there is, which is what a position no rule reached admits. */
    AdmittedPlan ANY = new Everything();

    /** Nothing at all, which is what refuses a declaration. */
    AdmittedPlan NONE = new Nothing();

    /** Every value, as a plan. */
    record Everything() implements AdmittedPlan {}

    /** No value, as a plan. */
    record Nothing() implements AdmittedPlan {}

    /**
     * A set the rules wrote out: these values, or every value but these.
     *
     * <p>One arm for both, because what tells them apart is a question the set answers and not a
     * step this has to plan. Neither costs anything to put together with anything else — the values
     * are in hand, and asking a language whether it holds one of finitely many is a walk over that
     * value.
     */
    record Written(ValueSet set) implements AdmittedPlan {

        public Written {
            if (set == null || set.isAny() || set.isEmpty()) {
                throw new IllegalArgumentException(
                        "everything and nothing are said as themselves, not as a written set");
            }
            // A language is not one of these, and that is what makes them free. What a pattern
            // admits is `Accepting`, which is a thing to build; these are values the rules wrote
            // down, and two of them are put together by looking at what is in them.
            if (set instanceof ValueSet.Matching) {
                throw new IllegalArgumentException(
                        "a language is a plan to build and not a set the rules wrote out");
            }
        }
    }

    /** The strings a pattern accepts, which is the one thing here that has to be built. */
    record Accepting(PatternSyntax syntax) implements AdmittedPlan {

        public Accepting {
            if (syntax == null) {
                throw new IllegalArgumentException("a pattern is some syntax");
            }
        }
    }

    /** The strings a pattern does not accept. */
    record Refusing(PatternSyntax syntax) implements AdmittedPlan {

        public Refusing {
            if (syntax == null) {
                throw new IllegalArgumentException("a pattern is some syntax");
            }
        }
    }

    /**
     * What all of these admit, which is what rules stated together leave.
     *
     * <p>A set of parts and not a pair, because a meet is one connective however it was bracketed.
     * Two of them and more: {@link #meeting} refuses to make one of nought or one, since those are
     * every value and that one part.
     */
    record Both(Set<AdmittedPlan> parts) implements AdmittedPlan {

        public Both {
            parts = held(parts, "met");
        }
    }

    /** What any of these admits, which is what alternatives leave. */
    record Either(Set<AdmittedPlan> parts) implements AdmittedPlan {

        public Either {
            parts = held(parts, "joined");
        }
    }

    private static Set<AdmittedPlan> held(Set<AdmittedPlan> parts, String how) {
        if (parts == null || parts.size() < 2) {
            throw new IllegalArgumentException(
                    "a plan of one part is that part, so nothing here is " + how + " alone");
        }
        return Collections.unmodifiableSet(new LinkedHashSet<>(parts));
    }

    /** The plan that is one set already known. */
    static AdmittedPlan of(ValueSet set) {
        if (set.isAny()) {
            return ANY;
        }
        return set.isEmpty() ? NONE : new Written(set);
    }

    /**
     * What all of them admit, normalised.
     *
     * <p>Flattened, since a meet of meets is one meet; every value dropped, since it narrows
     * nothing; nothing kept whole, since a meet with it is nothing; and each part once, since a
     * rule stated twice says it once. What is left is the meet that actually has to be built.
     *
     * <p>Written sets are met with each other here, because that costs nothing and leaves less to
     * build. The result is one written set among the parts, wherever the rules wrote any.
     */
    static AdmittedPlan meeting(List<AdmittedPlan> parts) {
        Set<AdmittedPlan> out = new LinkedHashSet<>();
        ValueSet written = null;
        for (AdmittedPlan each : flattened(parts, true)) {
            switch (each) {
                case Nothing _ -> {
                    return NONE;
                }
                case Everything _ -> { }
                case Written it -> written = written == null ? it.set()
                        : Sets.metPlainly(written, it.set());
                default -> out.add(each);
            }
        }
        if (written != null) {
            if (written.isEmpty()) {
                return NONE;
            }
            if (!written.isAny()) {
                out.add(new Written(written));
            }
        }
        return one(out, true);
    }

    /** What any of them admits, normalised the same way and the other way round. */
    static AdmittedPlan joining(List<AdmittedPlan> parts) {
        Set<AdmittedPlan> out = new LinkedHashSet<>();
        ValueSet written = null;
        for (AdmittedPlan each : flattened(parts, false)) {
            switch (each) {
                case Everything _ -> {
                    return ANY;
                }
                case Nothing _ -> { }
                case Written it -> written = written == null ? it.set()
                        : Sets.joinedPlainly(written, it.set());
                default -> out.add(each);
            }
        }
        if (written != null) {
            if (written.isAny()) {
                return ANY;
            }
            if (!written.isEmpty()) {
                out.add(new Written(written));
            }
        }
        return one(out, false);
    }

    /** The parts of a plan of this connective, its own parts taken out of it. */
    private static List<AdmittedPlan> flattened(List<AdmittedPlan> parts, boolean met) {
        List<AdmittedPlan> out = new ArrayList<>();
        for (AdmittedPlan each : parts) {
            if (met && each instanceof Both it) {
                out.addAll(it.parts());
            } else if (!met && each instanceof Either it) {
                out.addAll(it.parts());
            } else {
                out.add(each);
            }
        }
        return out;
    }

    private static AdmittedPlan one(Set<AdmittedPlan> parts, boolean met) {
        if (parts.isEmpty()) {
            // Nothing was left to say: everything met with everything, or nothing joined with
            // nothing. Which of the two is the connective's own unit.
            return met ? ANY : NONE;
        }
        if (parts.size() == 1) {
            return parts.iterator().next();
        }
        return met ? new Both(parts) : new Either(parts);
    }
}
