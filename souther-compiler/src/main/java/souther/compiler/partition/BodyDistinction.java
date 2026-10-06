package souther.compiler.partition;

import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.reading.CoverageRead;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * How far a behavior's body tells apart the classes of one position of its input.
 *
 * <p>The third of three answers about a position, and none of them stands for another. Which
 * classes the position holds is the model's ({@link Axis#classes()}); which rules those classes were
 * composed out of is where they came from ({@link Axis#divides()}); this is what the behavior does
 * with them. A sum holds its cases because it is a sum, so a {@code match} over them composes no
 * class and leaves {@code divides} empty — and tells every case apart all the same.
 *
 * <p>A partition of the classes and not a count of them. A body that takes {@code A}, {@code B},
 * {@code C} and {@code D} and asks only whether a value is one of the first two tells the four apart
 * as two groups. So what is held is the groups: two classes are in one group where no way a run of
 * the body takes admits one of them and not the other.
 *
 * <p><b>Read off the ways runs take, through the lookup a cell is made by.</b> A way is the
 * decisions a run settles to get somewhere — a {@code match} on a case, a comparison a fork is
 * taken by — and which classes they leave together is what {@link InteractionCells} reads a
 * condition into. A decision tells apart only the values that arrive where it is made, so it is read
 * with the way it is on and never on its own ({@link WhatABodyTellsApart}).
 *
 * <p><b>What cannot be read is {@link Unread}, never {@link Untouched} and never a partition.</b> A
 * decision the reading could not name a subject for — a value no position is, a name bound over
 * several cases, an attempted construction — tells something apart about some position, and which
 * one is not known; so no position's partition is complete beside it. A partition read in part is
 * not said as though it were the whole.
 *
 * <p><b>And a rule the body wrote that no decision reads is said, not guessed at.</b> The predicate
 * handed to a {@code List.filter} divides a position into classes and the walk that finds the
 * decisions does not enter it, on purpose. What the body tells apart there is real and is not
 * something this reads into classes, so the position is {@link Unread} rather than one the body
 * tells nothing apart about.
 *
 * <p><b>And not where a value is used.</b> A position copied into the answer, or added to another,
 * is read by the body and told apart by nothing. A sum divides a position by being a sum, and a body
 * that never looks at it has said nothing about it.
 */
public sealed interface BodyDistinction {

    /** No way a run of the body takes says anything about the position, so every class goes one
     *  way. */
    record Untouched() implements BodyDistinction {}

    /**
     * Some way a run takes is about the position, and all of what is said there was read into
     * classes.
     *
     * @param groups the classes, each in the group of those no way a run takes tells it apart from,
     *               in the order of the first class of each and each in the order of the classes
     */
    record Drawn(List<List<String>> groups) implements BodyDistinction {

        public Drawn {
            groups = groups.stream().<List<String>>map(List::copyOf).toList();
        }
    }

    /**
     * What the body tells apart at the position is not known in full: something it says about the
     * position is not read into classes — a condition this compiler names the position of and
     * cannot place, a rule the body wrote that no decision reads — or a decision somewhere has a
     * subject the reading could not name, and may be about this position as readily as any other.
     *
     * @param readSoFar     the classes in groups as far as what was read tells them apart, which
     *                      is part of the answer and never the whole of it
     * @param unplacedHere whether something the body says about this position itself is what went
     *                      unread, as against a decision whose subject nobody could name
     */
    record Unread(List<List<String>> readSoFar, boolean unplacedHere) implements BodyDistinction {

        public Unread {
            readSoFar = readSoFar.stream().<List<String>>map(List::copyOf).toList();
        }
    }

    /** There is no body to read, so what the behavior tells apart is not known. */
    record NoBody() implements BodyDistinction {}

    /**
     * Whether a combination of this position's classes with another's is worth a row.
     *
     * <p>Where the body tells some of its classes apart, where it says something about the position
     * that was not read into classes, and where there is no body at all. A combination asks that
     * the behavior was tried with both classes at once, which is worth asking where the behavior
     * may tell them apart; a position whose classes all go one way answers the same however the
     * other moves, whether nothing in the body is about it or what is about it sends every class
     * alike. With no body, what is missing is the reading and not the relevance.
     *
     * <p>Not whether what is told apart is known in full, which is a different question. A decision
     * whose subject nobody could name leaves every position's answer open, and is no reason to ask
     * for a row combining a position nothing read is about with another.
     */
    default boolean makesCombinations() {
        return switch (this) {
            case Untouched _ -> false;
            case Drawn it -> it.groups().size() > 1;
            case Unread it -> it.unplacedHere() || it.readSoFar().size() > 1;
            case NoBody _ -> true;
        };
    }

    /** What a behavior with no body tells apart at each of {@code axes}, which is unknown. */
    static Map<AxisId, BodyDistinction> withoutABody(List<Axis> axes) {
        Map<AxisId, BodyDistinction> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            out.put(axis.id(), new NoBody());
        }
        return Map.copyOf(out);
    }

    /**
     * What the body read as {@code read} tells apart at each of {@code axes}, where
     * {@code noLine} is what the reading of the input found about the rules it drew no line for.
     *
     * <p>Read off the ways runs take and nothing else ({@link CoverageRead.Read#taken}). Taken from
     * the ways in to the arms or the meetings as well, a way no run takes would be read as a
     * decision the body makes.
     */
    static Map<AxisId, BodyDistinction> of(CoverageRead.Read read, List<Axis> axes,
                                           List<RuleWithoutALine> noLine) {
        return WhatABodyTellsApart.of(read, axes, noLine);
    }
}
