package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * The values that put a term at a number, which is the other direction of reading a
 * {@link NumericTerm} off an observation.
 *
 * <p><b>Not its inverse.</b> Reading is not injective and building cannot undo it: many strings are
 * five long, and every time in an hour falls in that hour. What holds is one way round — every value
 * built here reads back as the number it was built for. Written as an inverse, the second operation
 * to be added would have been the one that broke it, and the way it would have broken is a row
 * offered at an edge it does not stand on.
 *
 * <p>And whether anything exists to build is a third statement, declared of the operation
 * ({@code EveryAnswerItCanGiveHasASourceValue}) and asked where an edge is claimed to be writable.
 * A reader that took "there is an arm for this" for "this always builds" would promise a row for
 * every count of a {@code Set<Bool>}.
 *
 * <p>Here and not on the term. What a term is measured by and what it reads are answers about the
 * quantity; what a value of it looks like written down is the generator's, and a term that answered
 * it would name the generator's own vocabulary from {@code inputs} — a dependency the wrong way
 * round. What the term owes is the identity, which is the operation, and the arms below are keyed on
 * what {@code semantics} declares of it.
 */
final class TermRealizations {

    /** What building values that answer a number came to. */
    sealed interface Realization {

        /**
         * Values that answer it, and what was not built.
         *
         * <p>Two halves of one answer, as {@link Witnesses.Sized} keeps them. A caller reading only
         * the first says every value was refused where some were never built, which is a different
         * thing to tell an author.
         *
         * <p><b>Everything the offer leaves out, and not only what a figure refused.</b> A walk that
         * went everywhere it knows how to go and a walk a figure turned back both leave values a
         * reader was not shown, and the reader deciding whether every value was refused needs the
         * two alike. Which of them a figure came to be here by is what {@link Stopped} is told
         * apart by, and it is not this.
         */
        record Built(List<FixtureTemplate> values, java.util.Set<CompositionBudget> heldBack,
                     java.util.Set<CompositionRepertoire> notAllOf) implements Realization {

            public Built {
                values = List.copyOf(values);
                heldBack = java.util.Set.copyOf(heldBack);
                notAllOf = java.util.Set.copyOf(notAllOf);
                if (values.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a realization that built nothing is one that built none, and says why");
                }
            }

            Built(List<FixtureTemplate> values, java.util.Set<CompositionBudget> heldBack) {
                this(values, heldBack, java.util.Set.of());
            }

            static Built whole(List<FixtureTemplate> values) {
                return new Built(values, java.util.Set.of());
            }
        }

        /**
         * A budget of this compiler's stopped the composing, and no value came of it.
         *
         * <p>Apart from {@link None} and the difference is the whole of why this is here. Both are
         * nothing built; only this one is a policy of this compiler's having run out, and only a
         * policy running out leaves the question of whether a value exists open in a way somebody
         * could act on by raising it.
         *
         * <p><b>So a figure is here only where a candidate was in front of the walk and this figure
         * left no room for it.</b> Raise it and that candidate gets tried — which is what makes the
         * word one an author can act on. A population this compiler walks some of stopped nothing
         * and is never a figure: it travels beside them ({@code notAllOf}) where a figure was met as
         * well, and where none was it is {@link Unexhausted} rather than anything here.
         *
         * <p>Never where a value was built. A budget that cut an offering short after something was
         * composed is {@link Built#heldBack()}: what it stopped is the rest of the offer, and the
         * point it was composed for has a value at it either way.
         */
        record Stopped(java.util.Set<CompositionBudget> by,
                       java.util.Set<CompositionRepertoire> notAllOf) implements Realization {

            public Stopped {
                by = java.util.Set.copyOf(by);
                notAllOf = java.util.Set.copyOf(notAllOf);
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a composing this compiler stopped says which budget stopped it");
                }
            }

            Stopped(java.util.Set<CompositionBudget> by) {
                this(by, java.util.Set.of());
            }
        }

        /**
         * Nothing was composed, and what this walked was some of what there is to walk.
         *
         * <p>Apart from {@link None}, and the difference is what a reader may conclude. Nothing was
         * refused by a figure, so there is no number to raise; and nothing here looked at every
         * value the point has, so an emptiness this came to establishes nothing about the model.
         * Told as {@code None}, a reader acts on a search that never wrote most of what it was
         * searching.
         *
         * <p>Apart from {@link Stopped} for the same reason in the other direction. A figure is
         * somebody's to raise and reaches what the search was holding; what reaches the rest of one
         * of these is somebody writing the rest, which is not work an author of a model can do.
         *
         * @param detail what this walk found, or null where it has nothing to add
         */
        record Unexhausted(java.util.Set<CompositionRepertoire> notAllOf, String detail)
                implements Realization {

            public Unexhausted {
                notAllOf = java.util.Set.copyOf(notAllOf);
                if (notAllOf.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a walk that says it saw some of them says some of what");
                }
            }
        }

        /**
         * Nothing here writes a value answering it, and no budget of this compiler's is why.
         *
         * <p>Which is a walk that looked everywhere it was going to look and found nothing, and not
         * one that declined to look. A figure may still have bounded what it offered — the ways a
         * total is spread are two of the many however far a search runs — and that is a thing to
         * say about an offer rather than a reason there is none.
         *
         * <p>The word is how a reader downstream treats it and {@code detail} is what happened in
         * this attempt, which is the arrangement {@link Generator.UnresolvedCombination} has. A
         * word read for the shape of the question outlives whatever made it true, so what a reader
         * is owed beyond it is evidence rather than another word.
         *
         * @param detail what this walk found, or null where it has nothing to add to the word. Two
         *               of these that came about differently do not carry the same sentence: a
         *               reader told the same thing twice is the reader working the difference out
         *               from an absence
         */
        record None(Generator.UnresolvedCombination.Reason why, String detail)
                implements Realization {

            None(Generator.UnresolvedCombination.Reason why) {
                this(why, null);
            }
        }
    }

    /**
     * Whether one value of a root answers all of these numbers at once.
     *
     * <p><b>Asked before anything is built, the way its neighbour above is.</b> A row writes one
     * value where a location is, so a location asked for two numbers is answered by composing a
     * value that has both or by nothing at all. Which of those it is turns on what the numbers are
     * taken as, and that is this file's question: the composer's is where the value goes.
     *
     * <p>The parts of a time and the parts of a date are the ones a value can be built to have
     * together. Not because they are independent — the parts of a time are and the parts of a date
     * are not, since a day of the month runs as far as that month goes and February goes further in
     * a leap year — but because each of them is a place in what a time and a date are spelled in,
     * and a value can be built with those places asked for at once. Whatever the parts do to each
     * other is the calendar's, and {@link #dateOn} is where it is answered.
     *
     * <p>Anything else is refused here rather than tried and found wanting: how long a string is is
     * no place in the spelling of a string, and a value answering both a length and an order is not
     * something below builds.
     *
     * <p>Distinct parts, which is what makes them independent. Two asks at one part are two asks
     * for one number and are the same target, so a group holding a part twice is a group somebody
     * built by hand.
     *
     * <p>One target is always together with itself, so a caller need not ask whether it has more
     * than one before asking this.
     */
    static boolean oneValueAnswersThemTogether(Collection<RealizationTarget> targets) {
        if (targets.size() <= 1) {
            return true;
        }
        Set<TakenAs.TimePart> times = new java.util.LinkedHashSet<>();
        Set<TakenAs.DatePart> dates = new java.util.LinkedHashSet<>();
        for (RealizationTarget target : targets) {
            if (!(target.term() instanceof NumericTerm.TakenOf taken)) {
                return false;
            }
            switch (taken.takenAs()) {
                case TakenAs.PartOfTime part -> times.add(part.part());
                case TakenAs.PartOfDate part -> dates.add(part.part());
                // A quotient is here rather than beside the parts. Two of them at one place do
                // leave values that answer both — a whole number divides by two and by three at
                // once — and working out which is solving for a value from two numbers of it,
                // which is not what putting parts side by side does.
                case TakenAs.HowManyItHolds _, TakenAs.TheSumOfWhatItHolds _,
                        TakenAs.TheTruncatingQuotient _ -> {
                    return false;
                }
            }
        }
        return times.size() + dates.size() == targets.size()
                && (times.isEmpty() || dates.isEmpty());
    }

    /**
     * The values to write at one root so that every one of these numbers is its answer.
     *
     * <p><b>One call for the whole of what a location was asked for.</b> Asked once per number and
     * the answers combined afterwards, there is nothing to combine: two values were built for one
     * place and the row holds whichever was written last, which is the point answered for one of
     * its numbers and offered as answered for both.
     *
     * <p>A group of one is {@link #at}, and is not a second way of doing what that does. Every
     * location the composer writes comes through here, so the case that grew the vocabulary is the
     * case with one number in it rather than the case the code was written for.
     *
     * <p>What a group this cannot build together comes back as is a root nothing composes a value
     * for, which is what {@link #oneValueAnswersThemTogether} says before a caller gets here — so a
     * caller that asked is not told anything it could have avoided asking for.
     *
     * <p>What each number is measured on is read per term and not handed in, for the reason the
     * single one reads it: a term this reading measures somewhere else is a term whose value would
     * be written on a carrier a caller found elsewhere.
     */
    static Realization together(Type sourceType, SequencedMap<RealizationTarget, Place> demands,
                                Quantities measuring,
                                souther.compiler.inputs.SearchRegion within,
                                RuleReadingContext reading) {
        SequencedMap<RealizationTarget, NumericSet> asked = new LinkedHashMap<>();
        for (Map.Entry<RealizationTarget, Place> each : demands.entrySet()) {
            asked.put(each.getKey(), new NumericSet.At(each.getValue()));
        }
        return allSatisfying(sourceType, asked, measuring, within, reading);
    }

    /**
     * The values to write at one root so that each of these numbers is one of the set asked for it.
     *
     * <p><b>The sets, and never a member of one picked beforehand.</b> A caller that chose a number
     * out of each set and asked for those would be asking whether one value answers that tuple, and
     * a no to that is no answer about the sets: the parts of a date are not independent, so the
     * second of February and the thirtieth of a month are each a date and are not one. Read as an
     * answer about the sets, a combination the calendar admits comes back as one nothing writes.
     *
     * <p>What each account does with a set is its own. Which numbers a value can be built at is
     * what an account knows — a part of a time runs as far as the part does, a count runs from
     * none — so the account walks its own numbers and asks the set which of them the rules admit.
     * Written here instead, this would be the one place that knows what every account's numbers
     * are, which is the switch below saying it does not.
     */
    static Realization allSatisfying(Type sourceType,
                                     SequencedMap<RealizationTarget, NumericSet> demands,
                                     Quantities measuring,
                                     souther.compiler.inputs.SearchRegion within,
                                     RuleReadingContext reading) {
        if (demands.size() == 1) {
            Map.Entry<RealizationTarget, NumericSet> one = demands.firstEntry();
            return satisfying(sourceType, measuring.ordersOf(one.getKey().term()), one.getValue(),
                    within, reading);
        }
        if (sourceType == null || !oneValueAnswersThemTogether(demands.keySet())) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Map<TakenAs.TimePart, NumericSet> times = new LinkedHashMap<>();
        Map<TakenAs.DatePart, NumericSet> dates = new LinkedHashMap<>();
        Carrier observed = null;
        for (Map.Entry<RealizationTarget, NumericSet> each : demands.entrySet()) {
            TermOrders orders = measuring.ordersOf(each.getKey().term());
            if (orders == null || !(each.getKey().term() instanceof NumericTerm.TakenOf taken)) {
                return new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            // The root's, and one root has one. Read off each term because that is where a reading
            // answers it, and the same answer each time round is what being one location means.
            observed = orders.observed();
            switch (taken.takenAs()) {
                case TakenAs.PartOfTime part -> times.put(part.part(), each.getValue());
                case TakenAs.PartOfDate part -> dates.put(part.part(), each.getValue());
                case TakenAs.HowManyItHolds _, TakenAs.TheSumOfWhatItHolds _,
                        TakenAs.TheTruncatingQuotient _ -> {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
            }
        }
        return times.isEmpty()
                ? onThoseParts(dates, sourceType, observed, reading.source())
                : atThoseParts(times, sourceType, observed, reading.source());
    }

    /**
     * The values to write at {@code target}'s root so that its number is {@code answer}, given what
     * the root holds.
     *
     * <p><b>The one owner of what puts a number where a search asked for it.</b> Which target it is
     * says which value is rebuilt; what is written into that value is the account the operation
     * declares. Exhaustive over both, with no {@code default}, so a term of a new kind and an
     * account added to the language are each questions this file has to answer rather than
     * conditions falling to whichever arm was written last.
     *
     * <p>A target that exists and a target nothing writes at are two different sentences, and both
     * of them are said here. {@link RealizationTarget} answers the first for every number there is;
     * the second is a {@link Realization.None}, a {@link Realization.Stopped} or a
     * {@link Realization.Unexhausted}, which differ in what a reader may do about it and not in
     * whether a value was written.
     */
    static Realization at(Type sourceType, TermOrders orders,
                          Place answer, souther.compiler.inputs.SearchRegion within,
                          RuleReadingContext reading) {
        return satisfying(sourceType, orders, new NumericSet.At(answer), within, reading);
    }

    /**
     * The values to write at {@code orders}' root so that its number is one of {@code wanted}.
     *
     * <p>The one owner of what puts a number where a search asked for it, and {@link #at} is the
     * case where the set asked for is one number. Exhaustive over the kinds of term and, below,
     * over the accounts, with no {@code default} — so a term of a new kind and an account added to
     * the language are each questions this file has to answer rather than conditions falling to
     * whichever arm was written last.
     *
     * <p><b>Nothing built is not nothing to build.</b> An account walks the numbers of the set it
     * can build for, in the order it would offer them, and stops at the first one that builds. What
     * it says when none of them did turns on whether it walked all of them: a set it exhausted is a
     * {@link Realization.None}, and one it stopped short of is a {@link Realization.Unexhausted},
     * which no reader may take for a statement about the model.
     */
    static Realization satisfying(Type sourceType, TermOrders orders, NumericSet wanted,
                                  souther.compiler.inputs.SearchRegion within,
                                  RuleReadingContext reading) {
        if (sourceType == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Which number is being written for, read off the answer that says which number it is of.
        // Handed in beside it, it was a second name for the same thing and a caller could give two
        // — and this would then write a value for one number on the order of another.
        RealizationTarget target = RealizationTarget.of(orders.term());
        return switch (target.term()) {
            // Written by the carrier the line was drawn on, and wearing every name the position
            // declares. Read off the boundary's own shape instead, a count on one carrier could be
            // written as a literal of another — which is how a date-time's second count reached a
            // row as an `Int`, and the decoder refused it with the report saying only that every
            // value tried had been refused.
            case NumericTerm.ValueOf _ -> standing(sourceType, orders, wanted, within, reading);
            case NumericTerm.TakenOf taken -> taken(taken.takenAs(), taken.arguments(), sourceType,
                    orders, wanted, within, reading);
            case NumericTerm.TakenOver over -> overARun(over.takenAs(), sourceType, orders,
                    wanted, within, reading);
        };
    }

    /**
     * A value of the position itself standing at one of those numbers.
     *
     * <p>Chosen against the carrier and inside what the rules leave, which is the search a class of
     * such a position is cut by and is asked here the same way. The order's own ends come from the
     * region, since where a row may be written is what says how far the values run — worked out
     * from the type instead, this would answer about wherever that type came from.
     */
    private static Realization standing(Type sourceType, TermOrders orders, NumericSet wanted,
                                        souther.compiler.inputs.SearchRegion within,
                                        RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        Carrier carrier = orders.answered();
        Place chosen = placeIn(wanted, orders, within);
        return chosen == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : oneValue(FixtureTemplate.on(carrier, chosen, ruleSource.symbols().scope()::reach),
                        sourceType, ruleSource);
    }

    /** One of those numbers on the carrier, or null where the search named none. Which number it
     *  is of is the orders', which is where the pair says so. */
    private static Place placeIn(NumericSet wanted, TermOrders orders,
                                 souther.compiler.inputs.SearchRegion within) {
        if (wanted instanceof NumericSet.At one) {
            return one.value();
        }
        if (!(wanted instanceof NumericSet.InARun run)) {
            // The values a rule singled out leave a set with no run to search, and what stands at
            // the position is chosen against the carrier by the reader that holds those values.
            return null;
        }
        NumericDomain.Bounds leaves = within == null ? null : within.runsBetween(orders.term());
        return new Criterion.Within(run.run(), null, Towards.ABOVE).somewhereInside(
                orders.answered(),
                leaves == null ? null : leaves.min(), leaves == null ? null : leaves.max());
    }

    /**
     * The values a given operation answers a number at.
     *
     * <p>One arm per declared account of what such an operation takes, and no default — the same
     * closure the reading is under, so an account added to {@code semantics} cannot be read off a
     * row without also being writable onto one. Split between two switches that did not have to
     * agree, an operation would have gained a boundary nobody could write a row for, and the report
     * would have said only that every value tried was refused.
     */
    private static Realization taken(TakenAs how, TakenArguments arguments, Type sourceType,
                                     TermOrders orders, NumericSet wanted,
                                     souther.compiler.inputs.SearchRegion within,
                                     RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        return switch (how) {
            // A container has no order of its own and is built out of what it holds, so this arm
            // takes none. That is the arm's own answer and not an order standing in for nothing.
            case TakenAs.HowManyItHolds _ -> holding(sourceType, wanted, orders, reading);
            // A container whose elements come to the total, which is what a row has to hold for
            // this number to be there. What that takes is choosing how many elements and what each
            // of them holds — one question whether the number is added up out of the container
            // itself or out of a path inside its elements, and answered for both in one place.
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(wanted, sourceType, orders, within,
                    reading);
            // And this one writes on the order the value is written on. Written on the order the
            // answer is measured on, the thirteenth hour would be offered as the thirteenth second —
            // the same mistake the reading makes in the other direction, which is why the pair
            // travels this far and the arm takes the end (#1027).
            case TakenAs.PartOfTime taken -> atThoseParts(Map.of(taken.part(), wanted), sourceType,
                    orders.observed(), ruleSource);
            case TakenAs.PartOfDate taken -> onThoseParts(Map.of(taken.part(), wanted), sourceType,
                    orders.observed(), ruleSource);
            // And this one multiplies back. What a quotient is taken of is a whole number and what
            // it answers is one, so both ends are the order the value is written on.
            case TakenAs.TheTruncatingQuotient taken ->
                    atThatQuotient(taken.read(arguments), sourceType, orders.observed(), wanted,
                            ruleSource);
        };
    }

    /**
     * The first of {@code numbers} a value was built for, or what came of trying all of them.
     *
     * <p><b>Where the difference between a set and a number of it is kept.</b> Nothing built at one
     * number says nothing about the next, so what this says when none of them built turns on
     * whether {@code everyOne} — whether the numbers handed in were all the set had in the window
     * the account can build over. They were, and nothing writes a value in the set; they were not,
     * and a figure of this compiler's is why, which is a thing an author can raise.
     *
     * <p>The reasons the attempts came back with travel either way. A budget met on the way to one
     * number is a budget met, whichever number was being tried, and a reader deciding what to do
     * about the offer reads it the same.
     */
    private static Realization firstThatBuilds(Tried tried,
                                               java.util.function.Function<Place, Realization> of) {
        Set<CompositionBudget> met = new java.util.LinkedHashSet<>();
        Set<CompositionRepertoire> some = new java.util.LinkedHashSet<>();
        Realization last = null;
        for (Place number : tried.numbers()) {
            Realization made = of.apply(number);
            if (made instanceof Realization.Built built) {
                return built;
            }
            last = made;
            switch (made) {
                case Realization.Stopped stopped -> {
                    met.addAll(stopped.by());
                    some.addAll(stopped.notAllOf());
                }
                case Realization.Unexhausted walked -> some.addAll(walked.notAllOf());
                case Realization.None _, Realization.Built _ -> { }
            }
        }
        if (!tried.everyOne()) {
            // The numbers past the figure were never tried, so nothing here is a statement about
            // the set. Said as the figure, which is what an author raises to have them tried.
            met.add(CompositionBudget.NUMBERS_OF_A_SET_TRIED);
        }
        if (!met.isEmpty()) {
            return new Realization.Stopped(met, some);
        }
        if (!some.isEmpty()) {
            return new Realization.Unexhausted(some,
                    last instanceof Realization.Unexhausted walked ? walked.detail() : null);
        }
        return last instanceof Realization.None none ? none
                : new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }

    /** A container whose elements come to one of those numbers, which is what a row has to hold for
     *  this number to be there. */
    private static Realization addingUp(NumericSet wanted, Type sourceType, TermOrders orders,
                                        souther.compiler.inputs.SearchRegion within,
                                        RuleReadingContext reading) {
        // From nought upward first, which is the order a reader would write them, and below nought
        // only where the rules leave nothing above it. A total is what its elements come to and may
        // be either side of nought, and a search that looked only upward would say a set of
        // negative totals holds nothing.
        //
        // Asked on the order the total is measured on, which a run of values answers a number over
        // and stands at no place of. Read on the order the values are written on instead, a total
        // taken over a run would be asked about a carrier the run has and the number does not.
        return firstThatBuilds(numbersToTry(wanted, orders.answered()),
                total -> ContainersAddingUp.to(total, sourceType, orders, within, reading));
    }

    /**
     * A value whose quotient by that divisor is that number: the number times the divisor.
     *
     * <p><b>A right inverse and not an inverse.</b> A run of values answers each quotient — half of
     * them where the divisor is two — and this writes one of them. What it owes is that what it
     * writes reads back as the number it was asked for, and the product does: dividing it by the
     * divisor leaves the quotient exactly, truncation or no truncation, because the product is a
     * multiple of what it is divided by. Which of the run this is is a choice about the value to
     * write down and not something the model said, as the first of January is for a year.
     *
     * <p>Where the product is past the end of what the position's own order holds, nothing is
     * composed. Asked of the carrier and not worked out here: what a whole number stops at is the
     * carrier's answer, and a value past it is one no row can write however the arithmetic came out.
     */
    private static Realization atThatQuotient(BigDecimal by, Type sourceType,
                                              Carrier observed, NumericSet wanted,
                                              RuleReadingSource ruleSource) {
        // A divisor that is not there, or is nought, is a term nothing built — what quotients there
        // are is settled where the account is asked for. Answered here as a place nothing composes
        // a value for, which is what a reader that got this far has somewhere to put.
        if (observed == null || by == null || by.signum() == 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // From nought outward on the side the set is on. A quotient whose product runs past what
        // the position's order holds is one nothing composes a value at, and the quotient next to
        // it may not be — so the set is walked rather than read at one of its numbers.
        return firstThatBuilds(numbersToTry(wanted, observed),
                quotient -> multipliedBack(by, sourceType, observed, quotient, ruleSource));
    }

    /** The numbers a search was handed, and whether they are all the set has.
     *
     *  @param numbers  what to try, in the order to try them
     *  @param everyOne whether the set held nothing else, which is what tells a set with no value
     *                  in it from a search that stopped short of one */
    private record Tried(List<Place> numbers, boolean everyOne) {}

    /**
     * The numbers of a set to try, nearest nought first on whichever side of it the set is.
     *
     * <p>A number of either sign is one an account here can be asked for, and a search that looked
     * one way would call a set of the other sign empty. Above nought first because that is the
     * order a reader would write them in, and the far side only where the near one holds none.
     *
     * <p>The figure is read once, here, and travels as whether the set was exhausted. Read again by
     * each account, the number a search was given and the number it reports against could part.
     */
    private static Tried numbersToTry(NumericSet wanted, Carrier on) {
        Tried above = numbersToTry(wanted, on, 0, Integer.MAX_VALUE);
        return above.numbers().isEmpty()
                ? numbersToTry(wanted, on, -Integer.MAX_VALUE, -1)
                : above;
    }

    /** The same over a window the caller's own kind of number runs between. */
    private static Tried numbersToTry(NumericSet wanted, Carrier on, int from, int to) {
        int many = CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum();
        List<Place> numbers = wanted.within(on, BigDecimal.valueOf(from),
                BigDecimal.valueOf(to), many);
        return new Tried(numbers, wanted.allOfThem(numbers, many));
    }

    /** The one value whose quotient by that divisor is exactly that number. */
    private static Realization multipliedBack(BigDecimal by, Type sourceType, Carrier observed,
                                              Place answer, RuleReadingSource ruleSource) {
        if (!(answer instanceof Count wanted)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Place dividend = observed.onTheGrid(new Count(wanted.at().multiply(by)));
        if (dividend == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return oneValue(
                FixtureTemplate.on(observed, dividend, ruleSource.symbols().scope()::reach),
                sourceType, ruleSource);
    }

    /**
     * The values a walk over a run answers a number at.
     *
     * <p>One arm per account, and no default, the way the taking of one value beside it is — the
     * same closure the reading of a run is under ({@code NumericTerm.TakenOver.readOver}), so an
     * account added to {@code semantics} cannot be read over a run without also being writable into
     * one.
     *
     * <p>And the arms answer alike on both sides. An account of a number taken of one value says
     * nothing about a run of them — which hour a run of times falls in is not a question — so the
     * reading answers that this is no number of theirs, and nothing composes a container for a
     * number nothing reads.
     */
    private static Realization overARun(TakenAs how, Type sourceType,
                                        TermOrders orders, NumericSet wanted,
                                        souther.compiler.inputs.SearchRegion within,
                                        RuleReadingContext reading) {
        return switch (how) {
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(wanted, sourceType, orders, within,
                    reading);
            case TakenAs.HowManyItHolds _, TakenAs.PartOfTime _, TakenAs.PartOfDate _,
                    TakenAs.TheTruncatingQuotient _ -> new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        };
    }

    /**
     * Values of the position holding as many as one of those numbers, which is {@link Witnesses}'
     * answer.
     *
     * <p>From none upward, which is the order the counts are offered in and the order a reader
     * would write them. A count a type cannot hold that many of is one this builds nothing at, and
     * the next count of the set is asked after it — so a set holding a count the type has no value
     * for is not a set nothing writes a value in.
     */
    private static Realization holding(Type sourceType, NumericSet wanted, TermOrders orders,
                                       RuleReadingContext reading) {
        return firstThatBuilds(numbersToTry(wanted, orders.answered()),
                count -> holdingExactly(sourceType, count, reading));
    }

    /** Values of the position holding exactly that many, which is {@link Witnesses}' answer. */
    private static Realization holdingExactly(Type sourceType, Place answer,
                                              RuleReadingContext reading) {
        int many = CountDomain.asCount(answer);
        if (many < 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        RuleReadingSource ruleSource = reading.source();
        TypeView holder = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(), ruleSource.published());
        // A name this module cannot write leaves no value to write, which is a position nothing
        // composes one for rather than a value written without the name. Asked of the position
        // before anything is built for it, since it is the same answer for every value.
        if (!(WornNames.of(holder.wrappers(), ruleSource) instanceof WornNames.Spelled worn)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Witnesses.Sized built = Witnesses.ofSize(holder, many, reading, Set.of());
        if (built.values().isEmpty()) {
            // Read off the build that was already done. `Witnesses` keeps what it made and why it
            // stopped as two halves of one answer for exactly this, and asking it again would be
            // the same decision taken twice — the two could not disagree today and there is no
            // reason to leave a second taking of it here.
            return built.heldBack().isEmpty()
                    ? new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Realization.Stopped(built.heldBack());
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : built.values()) {
            out.add(RepresentativeSource.under(worn.names(), each));
        }
        return new Realization.Built(out, built.heldBack());
    }

    /**
     * A time of day whose given parts stand at those numbers, with the parts beside them at nought.
     *
     * <p>One of the many, and not the many. Every time in that hour answers the same hour, and
     * which of them is offered is this reader's to choose — what it owes is that what it offers
     * reads back, not that it enumerates the inverse. Nought beside is the plain choice: the hour
     * on the hour.
     *
     * <p><b>Every part asked for at once, because the value is one value.</b> The parts of a time
     * are what one count of seconds is spelled in, so a value written for one of them and a value
     * written for another are the same value written twice — and the row that has to hold both is
     * holding whichever was written last. Adding them up is the whole of what taking them together
     * is: the parts do not overlap, so what each contributes to the count is what it contributes
     * whoever else was asked for.
     *
     * <p><b>And each part is chosen out of its own set on its own, because they are independent.</b>
     * Every hour goes with every minute, so a number admitted for one part is admitted whatever the
     * other parts came to — which is why this needs no search across them and why a part with
     * nothing admitted is a time nothing answers rather than a combination this did not find. The
     * parts of a date are not like this, and {@link #onThoseParts} is where that is answered.
     *
     * <p>The order is handed in and not named here. That what this is taken of is a time is the
     * arm's own condition and the library is held to it, but which carrier a time is written on is
     * {@link Carrier}'s one answer — named here, this would be a second place saying what a time
     * counts, and the two would part the day the first one moved.
     */
    private static Realization atThoseParts(Map<TakenAs.TimePart, NumericSet> parts,
                                            Type sourceType, Carrier observed,
                                            RuleReadingSource ruleSource) {
        if (observed == null || parts.isEmpty()) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        BigDecimal seconds = BigDecimal.ZERO;
        for (Map.Entry<TakenAs.TimePart, NumericSet> each : parts.entrySet()) {
            // The numbers this part runs between, which is what a value of it can be at all, and
            // the first of them the rules admit. Walked to the end, because a part is a handful of
            // numbers: a set that holds none of them is a set no time answers, which is a thing
            // this may say having looked at every one.
            List<Place> admitted = each.getValue().within(observed, BigDecimal.ZERO,
                    BigDecimal.valueOf(each.getKey().many() - 1L), 1);
            if (admitted.isEmpty()) {
                // Outside the parts a day has. Not this reader's to report as a refusal: what a
                // part runs between is the operation's declared bound, and a number outside it is a
                // number nothing answers.
                return new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            seconds = seconds.add(((Count) admitted.get(0)).at()
                    .multiply(BigDecimal.valueOf(each.getKey().seconds())));
        }
        FixtureTemplate standing = WornNames.under(
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(), ruleSource.published()).wrappers(),
                FixtureTemplate.on(observed, Count.of(seconds), ruleSource.symbols().scope()::reach),
                ruleSource);
        return standing == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : Realization.Built.whole(List.of(standing));
    }

    /**
     * A date whose given part stands at that number, with the parts beside it at the first they run
     * from.
     *
     * <p>One of the many, as the time above offers one of the many. Every date in the year answers
     * the same year, and what this owes is that what it offers reads back — not that it enumerates
     * the dates that would. The first of January is the plain choice, and it is a choice about which
     * value to write down rather than anything the model said.
     *
     * <p>A day of the month is offered in the longest month there is, so every day a date can fall
     * on is a day of the one this writes. Offered in a short month, the last days of the long ones
     * would be days no date has, and a rule about the thirty-first would have no witness for a
     * reason that is about this choice rather than about the calendar.
     *
     * <p>Whether a date can have the part at all is asked of the calendar and not of the bound the
     * operation declares. A bound is what the model may assume of an answer; what dates there are is
     * what a witness can be built from, and reading the second off the first would make a bound
     * loosened by hand into dates that cannot be written.
     */
    private static Realization onThoseParts(Map<TakenAs.DatePart, NumericSet> parts,
                                            Type sourceType, Carrier observed,
                                            RuleReadingSource ruleSource) {
        if (observed == null || parts.isEmpty()) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Search found = dateOn(parts, observed);
        if (found.on() == null) {
            // No date has parts the rules all admit. Which is a statement about the calendar where
            // every combination was looked at, and a statement about this compiler where it was
            // not — and the two are not the same thing to tell an author.
            return found.everyOne()
                    ? new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Realization.Stopped(
                            Set.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED));
        }
        FixtureTemplate standing = WornNames.under(
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(), ruleSource.published()).wrappers(),
                FixtureTemplate.on(observed, Dates.dayOf(found.on()),
                        ruleSource.symbols().scope()::reach),
                ruleSource);
        return standing == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : Realization.Built.whole(List.of(standing));
    }

    /**
     * The date this offers for those parts standing at those numbers, or null where no date has
     * them.
     *
     * <p>Asked of the calendar rather than tried and caught. What a year, a month and a day run
     * between is something {@code java.time} answers, and building a date to find out whether one
     * could be built is asking a question by reading the exception from the answer.
     *
     * <p><b>A part nobody asked for stands at the value that rules out the fewest of the parts that
     * were asked for.</b> The parts of a date are not independent the way the parts of a time are:
     * how far the days run depends on the month, and February's length depends on the year. So a
     * value chosen here for a part nobody asked for is not merely a value that part can take — a
     * date exists for every one of those — it is the one that leaves every combination the calendar
     * admits still writable. The longest month, and a year whose February is a day longer.
     *
     * <p>Chosen for a part alone, each of them would be right and the pair would not: a month and a
     * day asked for together would be offered in whichever year the month-alone case happened to
     * name, and the twenty-ninth of February would be a day the calendar has that nothing here
     * writes.
     *
     * <p>How far the days run is asked of the month the date is actually built in, and not of how
     * far a day of any month can run. Where no month was asked for that is the longest there is, so
     * every day a date can fall on is a day of the one this writes; where one was, the days are
     * that month's and a rule about the thirty-first of a short one has no witness because the
     * calendar has none.
     *
     * <p><b>Solved over the sets and not at one number of each.</b> The parts constrain each other,
     * so a combination the calendar refuses says nothing about the combinations beside it: the
     * second of February is a date nothing writes and the thirtieth of March is one that is
     * written, and both stand at a month at or after February and a day at or after the thirtieth.
     * Read at one number apiece, the first of those would be the answer for the pair of sets, and
     * a report would say the model asks for a date that does not exist.
     *
     * <p>The months and the days are walked to their ends, which is what makes an answer of nothing
     * a statement about the calendar. The years are not — there are more of them than anything here
     * will try — so a search that walked some of them says so, and the caller carries that out as a
     * figure rather than as an answer about the model.
     */
    private static Search dateOn(Map<TakenAs.DatePart, NumericSet> parts, Carrier observed) {
        // The years are more than anything here walks, so what comes back says whether it was all
        // of them; the months and the days are as many as the calendar has, so walking their window
        // is walking them.
        Tried years = parts.containsKey(TakenAs.DatePart.YEAR)
                ? numbersToTry(parts.get(TakenAs.DatePart.YEAR), observed,
                        java.time.LocalDate.MIN.getYear(), java.time.LocalDate.MAX.getYear())
                : new Tried(List.of(Count.of(BigDecimal.valueOf(A_LEAP_YEAR))), true);
        List<Place> months = numbersOf(parts, TakenAs.DatePart.MONTH, observed,
                MONTHS_A_YEAR_HAS, A_LONGEST_MONTH);
        List<Place> days = numbersOf(parts, TakenAs.DatePart.DAY, observed,
                DAYS_THE_LONGEST_MONTH_HAS, FIRST_OF_THE_MONTH);
        boolean everyOne = years.everyOne();
        for (Place year : years.numbers()) {
            for (Place month : months) {
                java.time.YearMonth in = java.time.YearMonth.of(
                        whole(year), whole(month));
                for (Place day : days) {
                    if (whole(day) <= in.lengthOfMonth()) {
                        return new Search(in.atDay(whole(day)), everyOne);
                    }
                }
            }
        }
        return new Search(null, everyOne);
    }

    /** A date this composed for those parts, or the reason there is none to report with.
     *
     *  @param on       the date, or null where the walk below found none
     *  @param everyOne whether the walk went over every combination the parts admit, which is what
     *                  tells a calendar that has no such date from a search that stopped short */
    private record Search(java.time.LocalDate on, boolean everyOne) {}

    /**
     * The numbers a part may stand at, in the order they are to be tried.
     *
     * <p>What the part runs between is the calendar's and is handed in; which of those the rules
     * admit is the set's. A part nobody asked for stands at the one value that rules out the fewest
     * of the parts that were asked for, which is a choice about the date to write and is why the
     * fallback is a number rather than the whole range.
     */
    private static List<Place> numbersOf(Map<TakenAs.DatePart, NumericSet> parts,
                                         TakenAs.DatePart part, Carrier observed,
                                         int asFarAs, int whenUnasked) {
        NumericSet wanted = parts.get(part);
        return wanted == null
                ? List.of(Count.of(BigDecimal.valueOf(whenUnasked)))
                : wanted.within(observed, BigDecimal.ONE, BigDecimal.valueOf(asFarAs), asFarAs);
    }

    private static int whole(Place at) {
        return ((Count) at).at().intValueExact();
    }

    /**
     * The year a month or a day is offered in.
     *
     * <p>Which year it is says nothing about a month on its own, and says one thing about a month
     * and a day together: February is a day longer in a leap year, so this is one. Offered in a
     * year that is not, the twenty-ninth of February would be a day the calendar has and no witness
     * could be written for.
     */
    private static final int A_LEAP_YEAR = 2000;

    /** January, which has as many days as any month has, so every day-of-month a date can fall on is
     *  a day of this one. */
    private static final int A_LONGEST_MONTH = 1;

    /** The day a year or a month is offered on. */
    private static final int FIRST_OF_THE_MONTH = 1;

    /** How far the months run, which is what a month may stand at whatever the rules leave it. */
    private static final int MONTHS_A_YEAR_HAS = 12;

    /** How far the days run in the longest month there is, which is as far as a day of any date
     *  runs. How far they run in the month a date is actually built in is asked of that month. */
    private static final int DAYS_THE_LONGEST_MONTH_HAS = 31;

    private static boolean within(java.math.BigDecimal answer,
                                  java.time.temporal.ChronoField field) {
        return within(answer, field.range().getMinimum(), field.range().getMaximum());
    }

    private static boolean within(java.math.BigDecimal answer, long from, long to) {
        return answer.compareTo(java.math.BigDecimal.valueOf(from)) >= 0
                && answer.compareTo(java.math.BigDecimal.valueOf(to)) <= 0;
    }

    /** One value, wearing every name the position declares, or the reason there is none. */
    private static Realization oneValue(FixtureTemplate bare, Type sourceType, RuleReadingSource ruleSource) {
        FixtureTemplate standing = WornNames.under(
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(), ruleSource.published()).wrappers(), bare, ruleSource);
        return standing == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : Realization.Built.whole(List.of(standing));
    }

    private TermRealizations() {}
}
