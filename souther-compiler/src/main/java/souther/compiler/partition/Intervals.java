package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Towards;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * Turning the lines a model draws through one numeric position into the ranges between them.
 *
 * <p>Several rules can cut the same position, and they are one partition however they were written.
 * {@code x < 0} and {@code x < 10} are three ranges, not two overlapping pairs, and a report built on
 * the pairs would count a value twice and never reach a hundred percent.
 *
 * <p>The type's own domain comes into it. A newtype's invariant bounds what can be constructed at all,
 * so a range outside it holds no value a row could write and is not a range to cover:
 *
 * <pre>invariant x &gt;= 0   with   guard x &lt; 10   is   0 &lt;= x &lt; 10  and  10 &lt;= x</pre>
 *
 * and not a third range below zero.
 */
final class Intervals {

    /** One range of a position's counts. A null bound is the domain's own edge. */
    record Interval(Place lo, boolean loInclusive, Place hi, boolean hiInclusive, Band of) {

        Interval(Place lo, boolean loInclusive, Place hi, boolean hiInclusive) {
            this(lo, loInclusive, hi, hiInclusive, null);
        }

        boolean holds(Place v) {
            if (lo != null) {
                int c = v.compareTo(lo);
                if (c < 0 || (c == 0 && !loInclusive)) {
                    return false;
                }
            }
            if (hi != null) {
                int c = v.compareTo(hi);
                return c < 0 || (c == 0 && hiInclusive);
            }
            return true;
        }

        /** Whether any value at all is in here. Two cuts at one place leave nothing between them. */
        boolean inhabited() {
            if (lo == null || hi == null) {
                return true;
            }
            int c = lo.compareTo(hi);
            return c < 0 || (c == 0 && loInclusive && hiInclusive);
        }

        /**
         * The class this range is, as a report names it.
         *
         * <p>Both ends written, each in whatever names it exactly. A line the position has a value
         * at is written as that value; one it has none at is written as the rule that drew it, in
         * numbers this language has — {@code 3 * x <= 1} rather than a third rounded to something
         * it is not. A run with one end of each kind says both and joins them, because an end left
         * out is a class that reads as holding the values past the next line along.
         */
        String label(Carrier carrier) {
            String low = lo == null
                    ? ruleEnd(of == null ? null : of.lower().seam(), Towards.ABOVE)
                    : carrier.written(lo) + (loInclusive ? " <= x" : " < x");
            String high = hi == null
                    ? ruleEnd(of == null ? null : of.upper().seam(), Towards.BELOW)
                    : (hiInclusive ? "x <= " : "x < ") + carrier.written(hi);
            if (low == null && high == null) {
                return "any";
            }
            if (low == null) {
                return high;
            }
            if (high == null) {
                return low;
            }
            // One subject and two relations where both ends can name the same one, which is what
            // an author reads a range as. Two subjects are two conditions and are said as two.
            String subject = subjectOf();
            return subject == null ? low + " and " + high
                    : low.substring(0, low.length() - subject.length())
                            + subject + high.substring(subject.length());
        }

        /** What both ends of this run relate a row to, where they relate it to the same thing.
         *  Null where one end names the position and the other a multiple of it. */
        private String subjectOf() {
            if (lo != null && hi != null) {
                return "x";
            }
            if (lo != null || hi != null || of == null) {
                return null;
            }
            ExactRatio shared = of.sharedMultiple();
            return shared == null ? null : times(shared);
        }

        /** One end as the rule that drew it, or null where nothing parts the run there. */
        private static String ruleEnd(Seam parted, Towards side) {
            return parted == null ? null : parted.asARuleAbout(Interval::times, side);
        }

        private static String times(ExactRatio by) {
            return by.equals(ExactRatio.ONE) ? "x"
                    : by.spelled() + " * x";
        }
    }

    /**
     * The ranges {@code thresholds} leave, inside what the position holds.
     *
     * <p>The outer ends are the position's own, and they are taken as they are: an end the position
     * stops short of is an end of the first range too, and rebuilding it as one the range holds puts
     * the value back that the rules had taken away. Thresholds outside what the position holds are
     * dropped — they cut a range no row can reach — and the end itself is outside it as much as
     * anything past it is.
     */
    static List<Band> of(List<Threshold> thresholds, Endpoint min, Endpoint max,
                         Carrier carrier) {
        // Keyed by where the values part, and not by the number a rule was written with. `x <= 4`
        // and `x < 5` divide the whole numbers once; keyed by their thresholds they are two splits,
        // and the range between them holds no value any row could be written at — a class a report
        // counts, tells an author no row is in, and asks the generator for (issue #880).
        //
        // Which subsumes the reason this was keyed by the number rather than by the count's own
        // equality: `0.00` and `0` are one number and part the values in one place.
        LevelSpace space = LevelSpace.onACarrier(carrier);
        List<Parting> parted = new ArrayList<>();
        for (Threshold each : thresholds) {
            // The division the rule made, taken as it was read rather than rebuilt from a number.
            // A rule that wrote a multiple of the position parts its values where the position may
            // hold none, and rebuilding the seam from a value of the position lost exactly those.
            parted.add(Parting.by(each.parts(), each.origin().authoredLine()));
        }
        // The one arrangement, which the points of every border on this position are read off as
        // well. Where the values part, in what order and with what left between them are questions
        // about the position, and deriving them twice is two chances to answer them differently —
        // which is how a border came to ask for a row inside a partition the classes had already
        // divided further along.
        List<Band> out = new ArrayList<>();
        for (Band run : QuantityArrangement.of(space, parted).bands()) {
            if (rangeOf(run, min, max).inhabited()) {
                out.add(run);
            }
        }
        return out.size() < 2 ? List.of() : List.copyOf(out);
    }

    /**
     * One run of the arrangement as a range of the position's counts.
     *
     * <p>The ends the rules leave rather than the ones the seams do: a run with nothing parting it
     * at one end stops where the position stops, and how far a bound reaches includes whether it
     * keeps its own value. A run parted at an end stops at the line, on the side the rule that drew
     * it keeps.
     */
    private static Interval rangeOf(Band run, Endpoint min, Endpoint max) {
        Endpoint low = run.lineBelow(min);
        Endpoint high = run.lineAbove(max);
        return new Interval(low == null ? null : low.at(), low == null || low.inclusive(),
                high == null ? null : high.at(), high == null || high.inclusive(), run);
    }

    /**
     * The classes those ranges are, on the term {@code of} at a position of {@code type}.
     *
     * <p>The orders say how a row's value is read into a number and how its numbers are spaced; the
     * type says what a value written at one of them looks like. A range of lengths has the first and
     * not the second: five is not what is written at the position, a string of five characters is,
     * and which values carry a count is asked of what builds them rather than settled here.
     *
     * <p>The orders are asked of the reading rather than handed in beside the term. Which order a
     * number is measured on follows from where the reading has that term standing, so a caller
     * working it out from whatever type reached it would be answering about wherever that type came
     * from — and a caller handing the answer over is handing two arguments that can be about two
     * terms.
     */
    static List<PartitionClass> classesOf(List<Band> runs, NumericTerm.FromOnePosition of,
                                          Type type, Quantities reading,
                                          RuleReadingContext ruleReading,
                                          Endpoint min, Endpoint max) {
        TermOrders orders = reading.ordersOf(of);
        // What the counts in a label stand for. A day count is a carrier and never a name for the
        // line, so the class an author reads is spelled in dates where the position holds them.
        Carrier carrier = orders.answered();
        List<PartitionClass> classes = new ArrayList<>();
        for (Band run : runs) {
            String label = rangeOf(run, min, max).label(carrier);
            String id = of + "/" + label;
            // The run's own answer about what is in it. Read off a range of the position's counts,
            // a class whose line falls at a place the position has no value for had no end to state
            // — so it held every value, and two such classes each held everything the other did.
            NumericSet admits = new NumericSet.InARun(run);
            Recognition is = new Recognition.OfACount(of, orders, admits);
            // Nothing composed here says what this compiler did not manage, and says nothing about
            // what the run holds. Above a string a rule stops short of, the order declines to name
            // a value on purpose — every string with that one as a prefix is greater, and choosing
            // between them puts a character nobody wrote into a row somebody reads. So the sentence
            // both empty answers carry is about composing: it is true of a run that holds nothing
            // as much as of one the order would not choose in, and it is the only one of the two
            // claims this compiler is in a position to make (ADR-0091).
            classes.add(PartitionClass.of(id, label, is,
                    standingFor(orders, admits, null, type, reading, ruleReading,
                            "a value whose " + measureOf(of) + " is in this range")));
        }
        // Classes of the number the runs are runs of, said here because here is where that is known.
        return classes.stream().map(each -> each.ofTheNumber(of)).toList();
    }

    /** What the range is a range of, in the words a reader of the report has: the operation where
     *  the number is what one answered, and the position's own value otherwise. */
    static String measureOf(NumericTerm.FromOnePosition of) {
        // Exhaustive, with no `default`. What a range is a range of is a word per kind of number,
        // so a kind added is one a reader has to be given a word for rather than one that arrives
        // under whichever word the condition left it on.
        return switch (of) {
            // The operation, and the whole term where the operation alone would not say which
            // number this is. What it was given beside the value is part of which number it is —
            // the quotient by two and the quotient by three are two — and the line this stands in
            // names the place and the range, so a taking given nothing beside the value is already
            // said by the operation and repeating the place there would say nothing.
            case NumericTerm.TakenOf taken ->
                    taken.arguments().none() ? taken.operation().qualified() : taken.toString();
            case NumericTerm.ValueOf _ -> "value";
        };
    }

    /**
     * Values of the position whose number on this term is one the class admits, or none where
     * nothing here writes one.
     *
     * <p><b>Asked of what writes a value at a number, rather than answered beside it.</b> What a
     * value reading as a number looks like is a construction per account of what the number is
     * taken as, and {@link TermRealizations} holds one arm per account with no default — so an
     * account the language gains is one a class of it is filled for by the same act that gives a
     * point of it a value. Answered here as well, the two switches did not have to agree, and this
     * one closed over the kinds of term instead: every number taken of a value went to the one
     * construction a count wants, so an hour of nine asked for a value holding nine of something.
     *
     * <p><b>The run, and not a number picked out of it.</b> A class holds every number between its
     * lines, and which of them a value is written at is a choice about the value. Made here, the
     * answer about the number this happened to pick was the answer about the class — so a class
     * holding a number nothing builds at beside numbers that build perfectly well came back as one
     * nothing writes a value in.
     *
     * <p>Where a row for one of these may be written is the reading's to say. It is asked for it
     * rather than handed a region a caller built, since a region worked out beside the reading is a
     * second answer to where the declarations leave room.
     *
     * <p><b>And what comes back short of values built is handed on as what it was.</b> A search
     * that looked everywhere it was going to look and a search a figure of this compiler's stopped
     * both leave a class with no value, and only the first is a thing to say about the model. Read
     * as one, the sentence an author gets says nothing writes a value in a range whose values this
     * compiler did not walk to — which is the shortfall reported as a fact about the model that
     * this file exists to have stopped doing.
     */
    static RepresentativeSource standingFor(TermOrders orders, NumericSet admits, Place named,
                                            Type type, Quantities reading,
                                            RuleReadingContext ruleReading, String what) {
        TermRealizations.Realization made = TermRealizations.satisfying(type, orders, admits,
                named, reading.region(), ruleReading);
        return switch (made) {
            case TermRealizations.Realization.Built built ->
                    RepresentativeSource.of(built.values());
            // Nothing writes one either way. That the rules leave no number of the class is more
            // than this says, and it is not this reader's to carry: what a representative is for
            // is standing in a class, and a class the rules leave nothing in has nothing to stand
            // in it whichever of the two is why.
            case TermRealizations.Realization.NoNumberTheRulesAdmit _,
                 TermRealizations.Realization.None _ ->
                    new RepresentativeSource.Ungeneratable("nothing here writes " + what);
            case TermRealizations.Realization.Stopped stopped -> new RepresentativeSource.NotReached(
                    stopped.by(), stopped.notAllOf(),
                    "nothing here composed " + what + ", which does not make one unwritable");
            case TermRealizations.Realization.Unexhausted some ->
                    new RepresentativeSource.NotReached(java.util.Set.of(), some.notAllOf(),
                            "nothing here composed " + what
                                    + ", which does not make one unwritable");
        };
    }

    private Intervals() {}
}
