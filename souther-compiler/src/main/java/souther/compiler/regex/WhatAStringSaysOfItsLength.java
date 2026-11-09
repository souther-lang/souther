package souther.compiler.regex;

import net.unit8.notation199x.pattern.PatternMeaning;

import java.util.ArrayList;
import java.util.List;

/**
 * What a string standing in a language, or inside another string, says of how long it is, on each
 * side of the statement.
 *
 * <p>The one place this is said. A guard over a call, what a type's invariant says of its values,
 * what the reading of a model says of a path and the proof over a library's laws each hold a
 * statement of this kind in a form of their own and want the same consequences of it; each maps
 * the {@link Condition}s into its own form and none restates what they are.
 *
 * <p>Conditions of a side, necessary and never sufficient: that every condition of the holding side
 * holds says nothing of whether the statement does, and the denied side's are not the denial of the
 * holding side's. A side with none says nothing.
 *
 * @param <S> what a string is called by the reader: a number of the call, a place, a value
 */
public final class WhatAStringSaysOfItsLength {

    /**
     * What a statement makes certain of each side of itself.
     *
     * @param ifHolds where the statement holds
     * @param ifDenied where it does not
     */
    public record Sides<S>(List<Condition<S>> ifHolds, List<Condition<S>> ifDenied) {

        public Sides {
            ifHolds = List.copyOf(ifHolds);
            ifDenied = List.copyOf(ifDenied);
        }

        /** A statement that says nothing of either side. */
        public static <S> Sides<S> nothing() {
            return new Sides<>(List.of(), List.of());
        }
    }

    /** One thing a side makes certain of the lengths, in code points. */
    public sealed interface Condition<S> {

        /** {@code string} holds at least {@code length} code points. */
        record AtLeast<S>(S string, long length) implements Condition<S> {}

        /** {@code string} holds at most {@code length} code points. */
        record AtMost<S>(S string, long length) implements Condition<S> {}

        /** {@code inner} holds no more code points than {@code outer}. */
        record NoLongerThan<S>(S inner, S outer) implements Condition<S> {}

        /** Nothing holds it: the side cannot be the one the statement comes out on. */
        record Impossible<S>() implements Condition<S> {}
    }

    private WhatAStringSaysOfItsLength() {
    }

    /**
     * {@code string} standing in the strings {@code meaning} accepts, or not.
     *
     * <p>Where it does it holds as many code points as the strings of the pattern do, and is none
     * where the pattern accepts none. Where it does not it is not the empty string if the pattern
     * accepts that, since nothing else of its length is left out.
     */
    public static <S> Sides<S> inALanguage(S string, PatternMeaning meaning) {
        LengthsOfAPattern.Bounds lengths = LengthsOfAPattern.of(meaning);
        if (lengths == null) {
            return new Sides<>(List.of(new Condition.Impossible<>()), List.of());
        }
        List<Condition<S>> ifHolds = new ArrayList<>();
        List<Condition<S>> ifDenied = new ArrayList<>();
        if (lengths.least() > 0) {
            ifHolds.add(new Condition.AtLeast<>(string, lengths.least()));
        }
        if (lengths.most() != null) {
            ifHolds.add(new Condition.AtMost<>(string, lengths.most()));
        }
        if (lengths.least() == 0) {
            ifDenied.add(new Condition.AtLeast<>(string, 1));
        }
        return new Sides<>(ifHolds, ifDenied);
    }

    /**
     * {@code inner} standing inside {@code outer}, or not; either one is null where the reader
     * names no length for it, and what needs it is left unsaid.
     *
     * <p>Where it does, the one inside holds no more code points than the one around it. Where it
     * does not, the one inside holds some, because the empty string stands inside every string.
     */
    public static <S> Sides<S> inside(S inner, S outer) {
        List<Condition<S>> ifHolds = inner == null || outer == null ? List.of()
                : List.of(new Condition.NoLongerThan<>(inner, outer));
        List<Condition<S>> ifDenied = inner == null ? List.of()
                : List.of(new Condition.AtLeast<>(inner, 1));
        return new Sides<>(ifHolds, ifDenied);
    }
}
