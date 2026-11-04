package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.PositionsAStatementReads.ReadSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

/**
 * The case a line of a statement of several decides in, where a row read back at a point of the
 * line has to be in it, with what it says of a remainder read once for each form and divisor
 * asked ({@link ResiduesAStatementLeaves}).
 *
 * <p>One for a line put to rows, asked at every value a point of it is searched with: the case is
 * the line's whatever value is tried, so what it says of a remainder is too.
 */
public final class TheCaseALineDecidesIn {

    private final Proposition decides;
    private final Map<ARemainder, WholeNumberRuns> read = new ConcurrentHashMap<>();

    TheCaseALineDecidesIn(Proposition decides) {
        this.decides = Objects.requireNonNull(decides, "a line decides in some case");
    }

    /** One remainder asked of the case: of a form by a divisor. */
    private record ARemainder(LinearForm<NumericTerm> dividend, BigInteger divisor) {}

    /** The remainders by {@code divisor} of {@code dividend} the case may hold at. */
    WholeNumberRuns remaindersOf(LinearForm<NumericTerm> dividend, BigInteger divisor) {
        return read.computeIfAbsent(new ARemainder(dividend, divisor),
                asked -> ResiduesAStatementLeaves.of(decides, asked.dividend(), asked.divisor()));
    }

    /** How many truths of the parts nobody settled are tried, past which the case is not refuted:
     *  a truth not tried is one it may hold at. */
    static final int TRUTHS_TRIED = 1 << 12;

    /**
     * What asking whether a row at a point along a way is in the case came to: a proof that none
     * is, or no claim at all. Not refuted is not a row: it says nothing of whether one is there.
     */
    public sealed interface CasePossibility {

        /** No row at the point along the way is in the case, shown as {@code by} says. */
        record Refuted(Refutation by) implements CasePossibility {}

        /** Nothing was shown either way. */
        record NotRefuted() implements CasePossibility {}

        CasePossibility NOT_REFUTED = new NotRefuted();
    }

    /** Which proof refuted the case at a point along a way. */
    public enum Refutation {

        /** The way holds no row with some part holding and none with it failing: it holds no row
         *  at all, whatever the point. */
        THE_WAY_HOLDS_NO_ROW,

        /** Under what the way and the point settle of the parts, no truth of the others makes the
         *  case hold, at any way a row stands at the point. */
        NO_TRUTH_OF_THE_PARTS_HOLDS_IT
    }

    /**
     * Whether a row at {@code point} along {@code way} may be in the case: refuted only where no
     * row there is, which is then shown, and not refuted wherever anything was left untried.
     *
     * <p>What is shown is that the way, the point and the case leave no input together. It is
     * shown of the case as it is written, part by part ({@link WhereAPartDecides#atomsOf}): the
     * statement a row read back is held to, so its parts hold together where it does and nowhere
     * else. Two parts that are equal are one statement and come out alike at a row. A part and its
     * denial are one question only where every row makes one of them hold and the other fail
     * ({@link Proposition#deniedWhereverItFails}); a statement on the applications of a closure
     * and its denial may both hold, or neither, and are two questions.
     *
     * <p>A part is a question only where what it is about is one thing wherever the case holds it:
     * then it comes out one way at a row, wherever it is held. What it reads tells
     * ({@link #oneStatementWhereverItIsHeld}): a place of the input, an element a quantifier of the
     * part ranges over, the element the case is read at and a value a binding holds where it is
     * read are each one subject throughout the case. A part whose reads are not known may read
     * what an application is handed, which is another value at each, and held twice in one case
     * it may be two statements spelled alike; it is no question, comes to no truth, and a case is
     * refuted only where it fails whichever way each place it is held at comes out.
     *
     * <p>All of it is of the line the case is asked of, as one reading of it: the way is the way
     * to that line, the case is what that reading decides in, and what a part asks of a row is
     * read off the comparison the line is drawn from, under whichever element or copy of a helper
     * it was read at, kept to what every copy asks ({@link ReachingCuts.WhatAnAtomSays}). So an
     * element the case is read at is the one the way and the part's meaning are read at.
     *
     * <p>Two things settle a question, and only as every row they are about makes it come out. The
     * way settles what it is shown to leave no row of: what a part holding asks of a row is every
     * row it holds of and maybe more ({@link ReachingCuts.WhatAnAtomSays}), so a way that leaves no
     * row with that holds none the part holds of, and the same of its denial
     * ({@link WayToTheBorder.Assuming#leavesNone}); a way that leaves none either way of a part
     * and its denial that are one question holds no row at all. The point settles what every row
     * standing at it makes of the part ({@link Standing#makesOf}), at each of the ways a row
     * stands at it, which together are every row there ({@link Standing#eachWayItStands}).
     *
     * <p>A row at the point along the way in the case would make the parts come out as those settle
     * them and the case hold: so where, at every way a row stands at the point, no truth of the
     * parts left open makes the case hold, there is no such row. A truth is tried by holding a part
     * open both ways, and a choice is refuted only where both ways of it are; where more truths
     * were to be tried than {@link #TRUTHS_TRIED}, nothing is refuted.
     */
    public CasePossibility possibilityAt(Standing point, WayToTheBorder.Assuming way,
                                         Function<Proposition,
                                                 Optional<ReachingCuts.WhatAnAtomSays>> says) {
        Parts parts = parts();
        Boolean[] settled = alongTheWay.computeIfAbsent(way,
                asked -> settledAlong(parts, asked, says));
        if (settled == NOWHERE) {
            return new CasePossibility.Refuted(Refutation.THE_WAY_HOLDS_NO_ROW);
        }
        List<Boolean[]> pieces = atThePoint.computeIfAbsent(point, asked -> madeAt(parts, asked));
        // Refuted below only by refuting a choice at some piece: a point taken apart into none
        // refuted nothing.
        if (pieces.isEmpty()) {
            return CasePossibility.NOT_REFUTED;
        }
        for (Boolean[] made : pieces) {
            Boolean[] truths = settled.clone();
            boolean agree = true;
            for (int at = 0; at < truths.length && agree; at++) {
                if (made[at] != null) {
                    agree = truths[at] == null || truths[at].equals(made[at]);
                    truths[at] = made[at];
                }
            }
            // Where the way and the point settle a part apart, no row is both along the way and
            // at this way of standing at the point.
            if (agree && !noTruthMakesItHold(decides, parts.asked(), truths)) {
                return CasePossibility.NOT_REFUTED;
            }
        }
        return new CasePossibility.Refuted(Refutation.NO_TRUTH_OF_THE_PARTS_HOLDS_IT);
    }

    /**
     * The parts of the case that are each one question ({@link #oneStatementWhereverItIsHeld}),
     * a part and its denial one where they are one question: {@code each} in the order met, and
     * {@code asked} each part where the case holds it, by identity, as the place of its question
     * in them, negated for a denial, and nought for a part that is no question of its own.
     */
    private record Parts(List<Proposition> each, Map<Proposition, Integer> asked) {}

    /** What the parts are, worked out the first time they are asked. */
    private volatile Parts parts;

    /** What each way asked of settles of each part, or {@link #NOWHERE} where the way holds no
     *  row with either; worked out once for a way, whichever point is asked along it. */
    private final Map<WayToTheBorder.Assuming, Boolean[]> alongTheWay =
            new ConcurrentHashMap<>();

    /** What a way that holds no row with a part or with its denial settles. */
    private static final Boolean[] NOWHERE = new Boolean[0];

    /** What each way a row stands at a point makes of each part, worked out once for a point
     *  whichever way it is asked along. */
    private final Map<Standing, List<Boolean[]>> atThePoint = new ConcurrentHashMap<>();

    /** What every row standing each way {@code point} is stood at makes of each part. */
    private static List<Boolean[]> madeAt(Parts parts, Standing point) {
        List<Boolean[]> out = new ArrayList<>();
        for (Standing each : point.eachWayItStands()) {
            Boolean[] made = new Boolean[parts.each().size()];
            for (int at = 0; at < made.length; at++) {
                made[at] = each.makesOf(parts.each().get(at)).orElse(null);
            }
            out.add(made);
        }
        return List.copyOf(out);
    }

    private Parts parts() {
        Parts had = parts;
        if (had == null) {
            List<Proposition> each = new ArrayList<>();
            Map<Proposition, Integer> asked = new HashMap<>();
            for (Proposition part : WhereAPartDecides.atomsOf(decides)) {
                if (!oneStatementWhereverItIsHeld(part)) {
                    continue;
                }
                Integer denied = Proposition.deniedWhereverItFails(part)
                        ? asked.get(part.denied()) : null;
                if (denied != null) {
                    asked.put(part, -denied);
                } else if (!asked.containsKey(part)) {
                    each.add(part);
                    asked.put(part, each.size());
                }
            }
            // Each part where the case holds it, as the very part held: a statement shares its
            // parts, and asked by its value a part is hashed as deep as it is, once for every
            // truth tried.
            Map<Proposition, Integer> held = new IdentityHashMap<>();
            Deque<Proposition> open = new ArrayDeque<>(List.of(decides));
            while (!open.isEmpty()) {
                Proposition one = open.pop();
                if (held.containsKey(one)) {
                    continue;
                }
                switch (one) {
                    case Proposition.All all -> {
                        held.put(one, 0);
                        open.addAll(all.parts());
                    }
                    case Proposition.Any any -> {
                        held.put(one, 0);
                        open.addAll(any.parts());
                    }
                    case Proposition.Always _ -> held.put(one, 0);
                    default -> held.put(one, asked.getOrDefault(one, 0));
                }
            }
            had = new Parts(List.copyOf(each), held);
            parts = had;
        }
        return had;
    }

    /**
     * Whether {@code part} says one thing wherever the case holds it: whether what it reads is
     * known ({@link PositionsAStatementReads#everyPlaceAndValueOf}). Every subject it can then
     * read is one subject throughout the case: a place of the input, an element of a container
     * — the one a quantifier of the part ranges over, or else the element the case is read at,
     * since one statement never holds two elements of a container under one spelling
     * ({@link Proposition.Some}) — or a value a binding holds where the case is read. What a
     * statement inside an application reads is the value that application is handed, and comes
     * to no reads known.
     */
    private static boolean oneStatementWhereverItIsHeld(Proposition part) {
        return PositionsAStatementReads.everyPlaceAndValueOf(part).isPresent();
    }

    /** What {@code way} settles of each part, as {@link #possibilityAt} reads it: nothing of a
     *  part reading a value a binding holds, which is no place the way says anything of. */
    private static Boolean[] settledAlong(Parts parts, WayToTheBorder.Assuming way,
                                          Function<Proposition,
                                                  Optional<ReachingCuts.WhatAnAtomSays>> says) {
        Boolean[] out = new Boolean[parts.each().size()];
        for (int at = 0; at < out.length; at++) {
            Proposition part = parts.each().get(at);
            if (PositionsAStatementReads.everyPlaceAndValueOf(part)
                    .map(reads -> reads.stream().anyMatch(ReadSubject.Bound.class::isInstance))
                    .orElse(true)) {
                continue;
            }
            Optional<ReachingCuts.WhatAnAtomSays> read = says.apply(part);
            if (read.isEmpty()) {
                continue;
            }
            boolean noneHolding = way.leavesNone(read.get().holding());
            if (!Proposition.deniedWhereverItFails(part)) {
                // A row may hold neither this nor its denial, or both: that none holds this says
                // nothing of its denial, which is a part of its own.
                out[at] = noneHolding ? Boolean.FALSE : null;
                continue;
            }
            boolean noneFailing = way.leavesNone(read.get().failing());
            if (noneHolding && noneFailing) {
                return NOWHERE;
            }
            out[at] = noneHolding ? Boolean.FALSE : noneFailing ? Boolean.TRUE : null;
        }
        return out;
    }

    /**
     * Whether no truth of the questions {@code truths} leaves unsettled makes {@code stated} hold:
     * {@code asked} is each part of it by identity, as the place of its question in
     * {@code truths}, negated for a denial and nought for a part that is no question. False
     * wherever more truths were to be tried than {@link #TRUTHS_TRIED}. {@code truths} is as it
     * was afterwards.
     */
    static boolean noTruthMakesItHold(Proposition stated, Map<Proposition, Integer> asked,
                                      Boolean[] truths) {
        return new Choosing(asked, truths).refuted(stated);
    }

    /** The truths of the parts, some unsettled, and how many of them were tried. */
    private static final class Choosing {

        private final Map<Proposition, Integer> asked;
        private final Boolean[] truths;
        private int tried;

        /** The first question met unsettled while working {@code stated} out, signed as it is
         *  held there; nought where none was. */
        private int firstOpen;

        Choosing(Map<Proposition, Integer> asked, Boolean[] truths) {
            this.asked = asked;
            this.truths = truths;
        }

        /**
         * Whether no truth of the unsettled parts makes {@code stated} hold. Refuted where it
         * fails under the truths settled; not where it holds, where it is still not settled with
         * no question left open in it, or past {@link #TRUTHS_TRIED}; and otherwise where a
         * question it leaves open is refuted holding and refuted failing.
         *
         * <p>The question chosen is the first one working it out met unsettled, and it is tried
         * first the way it is held there: a question working it out never meets is one no truth
         * of which settles it, and held that way the first one met goes the way that may make it
         * hold. Which is chosen decides how soon a truth making it hold is found, and not what is
         * refuted: a choice is refuted only where both ways of it are.
         */
        boolean refuted(Proposition stated) {
            firstOpen = 0;
            Boolean now = valueOf(stated, new IdentityHashMap<>());
            if (now != null) {
                return !now;
            }
            if (++tried > TRUTHS_TRIED || firstOpen == 0) {
                return false;
            }
            int at = Math.abs(firstOpen) - 1;
            Boolean held = firstOpen > 0;
            for (Boolean truth : List.of(held, !held)) {
                truths[at] = truth;
                boolean refuted = refuted(stated);
                truths[at] = null;
                if (!refuted) {
                    return false;
                }
            }
            return true;
        }

        /** No settled truth, as {@code worked} holds it: a part that comes to neither. */
        private static final Object OPEN = new Object();

        /**
         * What {@code stated} comes to under the truths settled, or null where that is not
         * settled — each part worked out once however many parts hold it, as {@code worked}
         * keeps it: a statement shares its parts, and walked as a tree it is as long as the ways
         * down it.
         */
        private Boolean valueOf(Proposition stated, Map<Proposition, Object> worked) {
            Object had = worked.get(stated);
            if (had != null) {
                return had == OPEN ? null : (Boolean) had;
            }
            Boolean out = valueOnce(stated, worked);
            worked.put(stated, out == null ? OPEN : out);
            return out;
        }

        private Boolean valueOnce(Proposition stated, Map<Proposition, Object> worked) {
            return switch (stated) {
                case Proposition.All all -> {
                    boolean open = false;
                    for (Proposition part : all.parts()) {
                        Boolean one = valueOf(part, worked);
                        if (Boolean.FALSE.equals(one)) {
                            yield false;
                        }
                        open |= one == null;
                    }
                    yield open ? null : true;
                }
                case Proposition.Any any -> {
                    boolean open = false;
                    for (Proposition part : any.parts()) {
                        Boolean one = valueOf(part, worked);
                        if (Boolean.TRUE.equals(one)) {
                            yield true;
                        }
                        open |= one == null;
                    }
                    yield open ? null : false;
                }
                case Proposition.Always(boolean holds) -> holds;
                // A part that is no question of its own comes to no settled truth: whatever is
                // refuted is refuted whichever way it comes out at each place it is held.
                default -> {
                    int signed = asked.get(stated);
                    if (signed == 0) {
                        yield null;
                    }
                    Boolean truth = truths[Math.abs(signed) - 1];
                    if (truth == null && firstOpen == 0) {
                        firstOpen = signed;
                    }
                    yield truth == null ? null : truth == signed > 0;
                }
            };
        }
    }
}
