package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * What a reading of where an expression stands came to.
 *
 * <p>A position reached is one. An expression that names none — arithmetic over a value, a branch
 * between two, something built — is the model saying there is nothing there, and a reader is told
 * so.
 *
 * <p><b>And a place this compiler could not choose between, which is neither of those.</b> A block
 * handed to two walks reads its element at one position on one run and another on the next, so the
 * expression names positions of the input and which of them is not settled. Held as no position, a
 * rule an author wrote about their input leaves the measurement without a word; held as one of them,
 * it is filed where the model may say nothing.
 *
 * <p>None of these stands for a shape the reading declined. That was an answer here once,
 * because a walk refused shapes for being shapes and a reader could not tell "this expression names
 * no position" from "this walk did not follow that". The walk now refuses a step for what a binding
 * is, and a binding that is nothing this can place is a fact about the model as much as arithmetic
 * over one is — so the ways such an answer could come back are shut where it would come from rather
 * than named here. Every shape a walk after a position meets is answered by an arm of its own, and a
 * shape added to {@link souther.compiler.core.Core} is one that walk does not compile without saying
 * what it names.
 *
 * <p><b>Read out arm by arm by a reader that needs a place, and never by one taking a step.</b>
 * Which position a line is drawn on, which position a claim is about, which position a run is over:
 * each of those needs one place and says so where it asks, and an answer added here does not compile
 * until it has. A reader whose question is where a value stands rather than which place it is has
 * nothing to decide, and asking it to decide is what quietly stops it deciding: such a walk is
 * written as one arm and a catch-all, and a catch-all is exhaustive whatever this gains. That step
 * is taken here ({@link #deeper}) so there is nothing for a catch-all to swallow.
 */
public sealed interface PathResolution {

    /**
     * Where the expression stands.
     *
     * <p>Somewhere, and refusing to be made without it. A position that is no position is what the
     * answer beside this one says, so a reader given one would be told a place was reached and find
     * the absence it is held apart from.
     */
    record At(TermPath path) implements PathResolution {

        public At {
            Objects.requireNonNull(path, "a position reached is somewhere");
        }
    }

    /**
     * The expression names no position of the input, which is a fact about the model.
     *
     * <p>What a rule about such a value comes to is a question elsewhere — it may have come from a
     * position, and where it did that is said ({@link InputReads#cameFrom}) — and this is the answer
     * that it does not stand at one.
     */
    record NotAPosition() implements PathResolution {}

    /**
     * The expression stands at each of {@code among} on some run of the model, and nothing here
     * says which of them any one read of it is.
     *
     * <p>A fact about this compiler and not about the model, which is why it is not the answer
     * beside it. A block handed to two walks has one parameter and two containers, so a name inside
     * it stands at one position of the input on one run and another on the next — the model is
     * perfectly clear and what cannot be worked out is which of them a reader should be sent to.
     *
     * <p><b>These are the positions it may stand at and not every place it may be.</b> A block
     * handed to a walk over the input and to a walk over a list written in the body stands at a
     * position on one of those runs and at none on the other, and that is this answer with one
     * position in it. So one of these does not say a read of the name is at a position — only that
     * a rule written under it is about these, wherever it is about the input at all.
     *
     * <p>Held apart from {@link NotAPosition} because everything a reader does with the two
     * differs. A rule about no position is one the model states nowhere and owes nothing; a rule
     * about one of these is a rule the model states, whose obligation stands at whichever of them
     * it turns out to be — so a measure over any of them is open until something says which.
     * Answered alike, a rule an author wrote about their input left the measurement without a word,
     * and every position it might have divided came back as one the model says nothing about.
     */
    record MayStandAt(List<TermPath> among) implements PathResolution {

        public MayStandAt {
            among = List.copyOf(among);
            if (among.isEmpty()) {
                throw new IllegalArgumentException(
                        "a value that may stand somewhere may stand at some place");
            }
        }
    }

    /**
     * The expression is made of what stands at every place of one of {@code alternatives}, the one
     * the run is on.
     *
     * <p>A reading of where a value came from, and never of where it stands ({@link
     * InputReads#cameFrom}). A fold from a map the input holds answers that map's entries on an
     * empty list and entries made of the list's elements otherwise, so what it answers came from
     * both places, and a rule about it is about a value made of them. Held apart from {@link
     * MayStandAt}, which says the value is at one of its places on the run it is on: this says it
     * is made of every place of an alternative. A fold over a list chosen between two is made of
     * its seed and the first list, or of its seed and the second, and that is two alternatives of
     * two places each.
     *
     * <p><b>One form for making and choosing, so that each takes what the other gave.</b> Every
     * place a value may be made of is in some alternative, an alternative made of one place being a
     * place it may stand at. {@link #madeOf} takes every alternative of each part with every
     * alternative of the others, {@link #anyOf} puts the alternatives of its cases side by side, and
     * all of them end in {@link #of}, so no combination is a case of its own to be handled or
     * forgotten. Some alternative has more than one place: an answer without one is a position or
     * several that it may stand at, and is that, however many.
     *
     * <p>Where making multiplies choices past {@link #MOST_WAYS_TOLD_APART}, the alternatives of
     * that value are one, made of every place of all of them. It is the places the value may be
     * made of and no fewer, so a rule about it is filed everywhere it is owed, and a reader that
     * asks only where the value came from cannot tell it from the exact answer.
     *
     * <p>Not a position, so a reader that needs one place reads it as none, as it does a value
     * that may stand at several.
     */
    record MadeOf(List<List<TermPath>> alternatives) implements PathResolution {

        public MadeOf {
            alternatives = alternatives.stream().map(List::copyOf).toList();
            if (alternatives.stream().anyMatch(List::isEmpty)
                    || alternatives.stream().noneMatch(each -> each.size() > 1)) {
                throw new IllegalArgumentException(
                        "a value made of several is made of more than one place on some run");
            }
        }

        /** Every place the value is made of on some run, once each. */
        public List<TermPath> places() {
            return alternatives.stream().flatMap(List::stream).distinct().toList();
        }
    }

    /**
     * The most alternatives that making a value out of several choices tells apart. Past that, the
     * alternatives are merged into one made of every place of every one of them: more places than
     * the value is made of on any run, and none fewer, which is what a rule about it is filed at.
     *
     * <p>A bound on the one operation that multiplies, {@link #madeOf}, where each choice made
     * between values doubles the alternatives of the value made of them. Choosing between values
     * only adds, so {@link #anyOf} has none, and a choice among any number of places stays the
     * places it may stand at. A bound and not a measurement: the choices a body writes by hand come
     * to a handful.
     */
    int MOST_WAYS_TOLD_APART = 64;

    /**
     * Where a value made of every one of {@code these} came from: the places of each together with
     * the places of the others, in every way the cases of each can come together.
     *
     * <p>A part that came from nowhere the input holds adds no place, as a constant written into
     * the body does not: the value came from the places of the others, and a rule about it is owed
     * the sentence there. It is no position only where every part is.
     */
    static PathResolution madeOf(List<PathResolution> these) {
        List<List<TermPath>> ways = List.of(List.of());
        boolean any = false;
        for (PathResolution each : these) {
            List<List<TermPath>> cases = alternativesOf(each);
            if (cases != null) {
                ways = together(ways, cases);
                any = true;
            }
        }
        return any ? of(ways, true) : new NotAPosition();
    }

    /** Every alternative of {@code ways} with every one of {@code cases}, or all their places in
     *  one alternative where two choices multiply past what an answer tells apart. One side that
     *  is not a choice multiplies nothing, however many alternatives the other has. */
    private static List<List<TermPath>> together(List<List<TermPath>> ways,
                                                 List<List<TermPath>> cases) {
        if (ways.size() > 1 && cases.size() > 1
                && (long) ways.size() * cases.size() > MOST_WAYS_TOLD_APART) {
            List<TermPath> every = new ArrayList<>();
            ways.forEach(every::addAll);
            cases.forEach(every::addAll);
            return List.of(every);
        }
        List<List<TermPath>> out = new ArrayList<>();
        for (List<TermPath> way : ways) {
            for (List<TermPath> one : cases) {
                List<TermPath> both = new ArrayList<>(way);
                both.addAll(one);
                out.add(both);
            }
        }
        return out;
    }

    /** The alternatives a value stands at or is made of, or null where it came from none. */
    private static List<List<TermPath>> alternativesOf(PathResolution resolution) {
        return switch (resolution) {
            case At(var at) -> List.of(List.of(at));
            case MayStandAt(var among) -> among.stream().map(List::of).toList();
            case MadeOf(var alternatives) -> alternatives;
            case NotAPosition _ -> null;
        };
    }

    /**
     * The answer for a value made of every place of one of {@code alternatives}, the one place of
     * all of them where {@code settled} and they come to one, and no position where there is none.
     *
     * <p>The one place every answer of this kind ends, so that a place dropped or repeated is
     * dropped or repeated once. Places of an alternative that are one place are one, alternatives
     * that are one are one, and an answer in which no alternative has more than one place is a
     * position or the positions it may stand at.
     */
    private static PathResolution of(List<List<TermPath>> alternatives, boolean settled) {
        List<List<TermPath>> ways = alternatives.stream()
                .map(each -> each.stream().distinct().toList()).distinct().toList();
        if (ways.isEmpty()) {
            return new NotAPosition();
        }
        if (ways.stream().anyMatch(each -> each.size() > 1)) {
            return new MadeOf(ways);
        }
        List<TermPath> places = ways.stream().map(List::getFirst).distinct().toList();
        return settled && places.size() == 1 ? new At(places.getFirst()) : new MayStandAt(places);
    }

    /**
     * Where a value that is any one of {@code these} stands.
     *
     * <p>One place where every one of them is that place, and the places among them otherwise. What
     * makes the second not the first is that a reader of one of these has no run in hand: the value
     * is what one of them is on the run it is on, so a place all of them agree about is where it
     * stands and anything less is where it may.
     *
     * <p><b>An answer of none among them does not take the rest away.</b> A block handed to a walk
     * over the input and to a walk over something the input has no part in is the caller's rule on
     * the first run whatever the second does, and the position it is about there is owed the
     * sentence. Dropped for the run that stands nowhere, a rule the author wrote about their input
     * would leave the measurement — which is what "all of them or none" came to.
     */
    static PathResolution anyOf(List<PathResolution> these) {
        List<List<TermPath>> ways = new ArrayList<>();
        boolean everyOne = true;
        for (PathResolution each : these) {
            List<List<TermPath>> cases = alternativesOf(each);
            if (cases == null) {
                everyOne = false;
            } else {
                ways.addAll(cases);
                everyOne &= each instanceof At;
            }
        }
        return of(ways, everyOne);
    }

    /**
     * Where a value that is whichever of {@code these} the run makes stands as a whole: the one
     * place every one of them is, and no position where any of them is elsewhere or nowhere.
     *
     * <p>Beside {@link #anyOf} and not one of its answers. That one is where a value may be, and a
     * case that holds none of it adds no place; this is where all of a value is on every run, and a
     * case that holds none of it is a run where the place is not all of it.
     */
    static PathResolution inEveryCase(List<PathResolution> these) {
        TermPath every = null;
        for (PathResolution each : these) {
            if (!(each instanceof At(var at)) || (every != null && !every.equals(at))) {
                return new NotAPosition();
            }
            every = at;
        }
        return every == null ? new NotAPosition() : new At(every);
    }

    /**
     * The same answer, with every narrowing to several cases on the way to the place taken out
     * ({@link TermPath#position}).
     *
     * <p>Where a value stands, as against how a fork reads it. A name an arm bound over
     * {@code Station} or {@code Hospital} stands for the value at the sum's position, and a field
     * every one of those cases spreads read off it is that field's name at the sum: what it is
     * compared with, what it is counted as and which position the body names are those, and the
     * name is crossed into the cases the way every name read at a sum is. That the arm left the
     * value two of the cases is what the way says, and a fork on the name is the one reader that
     * asks it ({@link InputReads#forkedOn}).
     */
    default PathResolution heldAt() {
        return switch (this) {
            case At(var at) -> new At(at.position());
            case NotAPosition _ -> this;
            // Each place it is made of, as a place; places that come to one are one place.
            case MadeOf(var alternatives) -> of(alternatives.stream()
                    .map(each -> each.stream().map(TermPath::position).toList()).toList(),
                    alternatives.size() == 1);
            // Each place it may stand at, as a place: the same answer about the run, whatever the
            // narrowings on the way to any one of them. Kept as the places it may be even where
            // they come to one, since what this says is that no read of it is settled as one.
            case MayStandAt(var among) -> of(among.stream().map(TermPath::position)
                    .map(List::of).toList(), false);
        };
    }

    /**
     * The same answer with {@code step} taken at every position it names.
     *
     * <p>For a reader whose question is about where a value stands rather than about which place it
     * is: a field of what stands here stands at the field of it, and an element of what stands here
     * at an element of it. Such a reader has nothing to decide between the answers — the step is
     * the same step wherever the value came from — so it says the step and this says where.
     *
     * <p><b>Written here because a reader that decides for itself stops deciding.</b> A walk over
     * the arms is exhaustive only while there is an arm for each, and a reader that took a step at
     * one answer and handed every other back untouched is exhaustive whatever this gains: an answer
     * naming several places came back naming those places without the step, and a rule written
     * about a field was filed at the value the field is in. So the step is taken once, here, and a
     * reader that needs one place asks for one place instead ({@link At}).
     */
    default PathResolution deeper(UnaryOperator<TermPath> step) {
        return switch (this) {
            case At(var at) -> new At(step.apply(at));
            case NotAPosition _ -> this;
            // What a value made of several places holds is made of what each of them holds, so a
            // step that reaches into every container takes the same step at each place. A step into
            // a field is not that: the places differ in what they are, and throughAField is the
            // one that says so.
            case MadeOf(var alternatives) -> of(alternatives.stream()
                    .map(each -> each.stream().map(step).toList()).toList(),
                    alternatives.size() == 1);
            // Still may, and still at each of them: a step taken at a place a value may stand is a
            // place a step of it may stand. Two of them the step takes to one place are one place
            // among the ones it may be, and it may still be none of them.
            case MayStandAt(var among) -> of(among.stream().map(step).map(List::of).toList(),
                    false);
        };
    }

    /**
     * The same answer for a field of the value, with {@code step} taken at the places it stands at.
     *
     * <p>A field of a value that stands at a place is at the field of that place, and of one that
     * may stand at several, at the field of each: it stands at one of them on the run it is on, and
     * that is the place whose value has the field. A value made of several places is made of
     * places that are not alike — a map's entries and the list elements a fold counted into it — so
     * a field of it is not known to be at the field of each, and a path through a field one of them
     * has none of names nothing. It is made of the places the value is, which is where a rule about
     * it is owed the sentence.
     */
    default PathResolution throughAField(UnaryOperator<TermPath> step) {
        return switch (this) {
            case MadeOf _ -> this;
            case At _, NotAPosition _, MayStandAt _ -> deeper(step);
        };
    }
}
