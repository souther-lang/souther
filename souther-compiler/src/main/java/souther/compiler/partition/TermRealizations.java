package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

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
         * Nothing was composed, and what this walked was not the whole of what there is to walk.
         *
         * <p>Which covers a walk that took no step in it at all. A group of numbers nothing here
         * writes a value for is a population this offered none of, and none is as far short of the
         * whole of it as some — what a reader may conclude is the same, and that is what the word
         * is for.
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
         * The rules admit no number of what was asked about, which is walked and not guessed.
         *
         * <p><b>About the numbers and not about the values.</b> Nothing was built because there was
         * nothing to build for: the walk went over every number the question holds and the rules
         * left none of them standing. A walk that had numbers and built at none of them is not
         * this — what that shows is about this compiler, and what this shows is about the model.
         *
         * <p><b>And about the question this attempt was for.</b> A location asked for a class and
         * a location asked for one number a caller picked out of one are two questions, and only a
         * walk of the first says anything of the first — which is what {@link AskedAt} keeps apart
         * and why the walk is only this where it covered what it was about.
         *
         * <p>Not a word a reader may print. What somebody is owed a row at is an obligation and a
         * search runs at a combination, so one of these settles the combination it came from and
         * the obligation is settled by what every combination of it came to. Published from here,
         * a class one combination of leaves nothing would be a class the rules leave nothing in,
         * while another combination of it goes on admitting values.
         */
        record NoNumberTheRulesAdmit() implements Realization {}

        /**
         * Nothing here writes a value answering it, and no budget of this compiler's is why.
         *
         * <p>Which is a walk that looked everywhere it was going to look and found nothing, and not
         * one that declined to look. A figure may still have bounded what it offered — the ways a
         * total is spread are two of the many however far a search runs — and that is a thing to
         * say about an offer rather than a reason there is none.
         *
         * <p><b>And everywhere it was going to look is not everywhere there is.</b> What a search
         * was handed is a set, and a set of one value is two different questions written the same
         * way: the value a rule singled out, and one value a caller picked out of a wider class to
         * try. Nothing here can tell them apart, so a walk that ran to the end of what it was
         * handed may have run to the end of one candidate — and this word is the one that says so
         * rather than the one that settles the class. What licenses a sentence about the model is
         * {@link Generator.UnresolvedCombination.Reason#THE_RULES_LEAVE_NOTHING_THERE}, and
         * nothing reaches it by counting what a walk refused.
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
     * How a value answering all of these numbers at once is written, and what is missing where
     * nothing writes one.
     *
     * <p><b>A capability of this compiler's and not a proposition about the model.</b> What this
     * answers is which way of writing one value there is for a group of numbers taken like these —
     * so a group it has no way for is a group nobody has written the solving for, and never a group
     * no value answers. Said as the second, a container asked for two of the totals inside it comes
     * back as a value that does not exist, which is a sentence about the model this has no standing
     * to say.
     *
     * <p><b>The way and not a yes.</b> What comes back of a group there is a way for is the way
     * itself, so the arms over what the numbers are taken as are here and the composer has none:
     * read a second time where the value is built, the two would be one classification written
     * twice and an account added to the language would reach a composer that had not heard of it.
     *
     * <p><b>Asked before anything is built, the way its neighbour above is.</b> A row writes one
     * value where a location is, so a location asked for two numbers is answered by composing a
     * value that has both or by nothing at all.
     *
     * <p><b>Which way it is follows from how the group's numbers are reached, and the arms below
     * are that rule rather than a list of shapes.</b> A number that is a place in the spelling of
     * what stands there is written at: the parts of a time and the parts of a date are places, so
     * a value can be built with all of them asked for at once — and whatever the parts do to each
     * other is the calendar's, which {@link #dateOn} answers. A number whose values come of a run
     * of the place's own is solved for out of the demands, which is what a quotient by a written
     * number is. A number read off a value the group already asks for is read off the values that
     * demand admits, which is what any number taken of a place is once the place's own value is
     * asked for beside it. A number what stands there is composed out of is composed for, which is
     * what how many a container holds and what it comes to are — a size the one leaves, filled to
     * the other. A group whose numbers are reached none of those ways is the population, and a way
     * of writing one is work nobody has done.
     *
     * <p>So a reader wanting to know what this compiler writes reads the arms and not this: a way
     * added is an arm, and a sentence here listing the ways would be a second answer that nothing
     * makes agree with them.
     *
     * <p>One target is a number on its own, and the way of writing a value for it is the one every
     * other reader of this file asks for — so a caller need not ask whether a group has more than
     * one member before asking this. A group of none is not a question: what is asked for is the
     * numbers of one location, and a location is asked for at least the number that brought a
     * caller here.
     */
    static JointRealization jointRealizationOf(Collection<RealizationTarget> targets) {
        // A builder is a thing a caller may call, so what comes back of a group with nothing in it
        // would be a way of writing a value for no number. Which is not a group nobody wrote the
        // solving for either: said as that, a caller that asked for nothing is told about this
        // compiler's repertoire.
        assert !targets.isEmpty() : "a group is the numbers of one location and has one of them";
        if (targets.size() == 1) {
            return new JointRealization.Supported(new JointBuilder.OneNumberOnItsOwn());
        }
        SequencedMap<RealizationTarget, TakenAs.TimePart> times = new LinkedHashMap<>();
        SequencedMap<RealizationTarget, TakenAs.DatePart> dates = new LinkedHashMap<>();
        SequencedMap<RealizationTarget, BigDecimal> quotients = new LinkedHashMap<>();
        // What stands at the place, where the group asks for it as well as for numbers taken of
        // it. One group has at most one of these: what a number of a place is taken of is the
        // place, so a second value asked for is a second place and is another group's.
        RealizationTarget itself = null;
        List<RealizationTarget> takenOfIt = new ArrayList<>();
        // How many the container holds and what it comes to, which are the two numbers a container
        // is composed out of rather than read for.
        RealizationTarget manyItHolds = null;
        RealizationTarget whatItComesTo = null;
        // Every target read before any of them is answered, because what the group is turns on all
        // of them. Decided as they come, a value asked for beside a length would be the group the
        // length is in or the group the value is in depending on which of them was read first.
        for (RealizationTarget target : targets) {
            switch (target.term()) {
                case NumericTerm.ValueOf _ -> itself = target;
                // A number taken over the values a walk came to is a number of a run, and a value
                // standing at one place is not a run — so there is nothing here to read it off.
                // What is added up over a run is still a number the container it runs through is
                // composed to have, though, and that is the arm below.
                case NumericTerm.TakenOver over -> {
                    if (!(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
                        return nothingSolvesAGroup();
                    }
                    whatItComesTo = target;
                }
                case NumericTerm.TakenOf taken -> {
                    takenOfIt.add(target);
                    switch (taken.takenAs()) {
                        case TakenAs.PartOfTime part -> times.put(target, part.part());
                        case TakenAs.PartOfDate part -> dates.put(target, part.part());
                        // A quotient is not a place in the spelling of anything, and putting two of
                        // them side by side writes no value: which value has both is solved for out
                        // of them. Which is what the arm below does, and it is the account's
                        // divisor that says what there is to solve. A divisor that reads as no
                        // number is a term this cannot solve for or read back, either way.
                        case TakenAs.TheTruncatingQuotient by -> {
                            BigDecimal divisor = by.read(taken.arguments());
                            if (divisor == null || divisor.signum() == 0) {
                                return nothingSolvesAGroup();
                            }
                            quotients.put(target, divisor);
                        }
                        // How much a container holds, which is what a container is composed out of
                        // rather than a place in the spelling of one: what answers a length and a
                        // total together is a container built to have both, and the arm below is
                        // where the two meet.
                        case TakenAs.HowManyItHolds _ -> manyItHolds = target;
                        case TakenAs.TheSumOfWhatItHolds _ -> whatItComesTo = target;
                    }
                }
            }
        }
        // The place's own value beside numbers taken of it, which is one question about one value.
        // What may stand there is what the place's own demand admits, and a number taken of one of
        // those values is what reading that value comes to — so the candidates are that demand's
        // and the rest of the group is read off each of them.
        if (itself != null) {
            RealizationTarget stands = itself;
            List<RealizationTarget> owned = new ArrayList<>(takenOfIt);
            owned.add(stands);
            return wholly(targets, owned,
                    () -> new JointBuilder.ItsOwnValueAndWhatIsTakenOfIt(stands, takenOfIt));
        }
        // How many a container holds beside what it comes to, which is one container to compose:
        // the sizes it may be are the ones the first number leaves, and filling one of those to
        // the second is what a total is composed by anyway.
        if (manyItHolds != null && whatItComesTo != null) {
            RealizationTarget many = manyItHolds;
            RealizationTarget total = whatItComesTo;
            return wholly(targets, List.of(many, total),
                    () -> new JointBuilder.HoldingThatManyAndAddingUpToThat(many, total));
        }
        // A quotient of a place beside a part of it is a value that is both a number and a moment,
        // and what would write one is neither arm here.
        if (!quotients.isEmpty()) {
            return wholly(targets, quotients.keySet(),
                    () -> new JointBuilder.SolvingForTheirQuotients(quotients));
        }
        // A value spelled in parts is written at the parts it is spelled in. Two asks at one part
        // are two asks for one number and are the same target, so a group holding a part twice is a
        // group somebody built by hand — not a population this compiler writes none of.
        assert Set.copyOf(times.values()).size() == times.size()
                && Set.copyOf(dates.values()).size() == dates.size()
                : "one part of one root is one number and one target";
        // The parts of a time beside the parts of a date are a value spelled two ways, and what
        // writes one is a builder for that spelling. Said as a group nobody wrote the solving for,
        // because that is what it is: the day an operation answers a part of each, the group is
        // owed a builder and this reports it rather than throwing.
        if (!times.isEmpty() && !dates.isEmpty()) {
            return nothingSolvesAGroup();
        }
        if (times.isEmpty() && dates.isEmpty()) {
            return nothingSolvesAGroup();
        }
        return wholly(targets, times.isEmpty() ? dates.keySet() : times.keySet(),
                () -> times.isEmpty() ? new JointBuilder.OnThoseDateParts(dates)
                        : new JointBuilder.AtThoseTimeParts(times));
    }

    /**
     * That way of writing one value, where the numbers it is a way for are the whole group.
     *
     * <p><b>One place asks it, because it is one contract.</b> What comes back of a group is a way
     * of writing a value for every number in it, and an arm that answered for some of them would
     * hand a caller a builder that leaves the rest unanswered — a row put at what half the group
     * asks for, offered as a row for all of it. Asked by each arm for itself, the arithmetic is
     * written as many times as there are arms and an arm added is a place for it to be left out:
     * which is what happened when a number taken over a run became one of the numbers a container
     * is composed for, and the arm above it went on answering for groups holding one.
     *
     * <p>So a group this bucketed into no arm's numbers is the population, and it gets there
     * without an arm having to notice. Which is the answer that is safe to reach by accident: a
     * way nobody wrote is a way nobody wrote, and the only thing lost is a builder somebody has yet
     * to write.
     */
    private static JointRealization wholly(Collection<RealizationTarget> group,
                                           Collection<RealizationTarget> owned,
                                           Supplier<JointBuilder> way) {
        return Set.copyOf(owned).equals(Set.copyOf(group))
                ? new JointRealization.Supported(way.get()) : nothingSolvesAGroup();
    }

    /**
     * What a group of numbers nothing here solves a value out of comes back as.
     *
     * <p>The population and not a word about the model, which is the whole of why this file answers
     * in this vocabulary: the values that answer several of their own numbers are ones this compiler
     * writes some of, and what reaches the rest is somebody writing the solving rather than an
     * author writing a row. Which of them it writes is the arms of {@link #jointRealizationOf} and
     * is not said again here.
     */
    private static JointRealization nothingSolvesAGroup() {
        return new JointRealization.Missing(
                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS);
    }

    /**
     * Which way of writing one value a group of numbers has, where it has one.
     *
     * <p>Two answers and not a yes and a no. A group there is a way for comes back with the way, so
     * nothing downstream classifies the group a second time; a group there is none for comes back
     * with the population this compiler offers none of, and a reader of that may conclude nothing
     * about whether a value exists.
     */
    sealed interface JointRealization {

        /** The way one value answering all of them is written. */
        record Supported(JointBuilder builder) implements JointRealization {}

        /**
         * Nothing here writes a value for this group, and the population it is part of.
         *
         * <p>Carried as a {@link CompositionRepertoire} because that is what it is — a set of
         * values this compiler produces some of rather than all of. What each caller says of it is
         * its own: this file answers a search in the words a search comes back in, and a reader
         * asking whether a row could reach a point has a vocabulary of its own for the same fact.
         */
        record Missing(CompositionRepertoire notAllOf) implements JointRealization {}
    }

    /**
     * A way of writing one value that answers a group of numbers of it.
     *
     * <p>Made where the group is classified and asked for the value where the row is composed, so
     * what the arms of that classification came to is carried rather than worked out twice. Which
     * numbers each of them is for is the group it was made from; what those numbers are asked to be
     * arrives with the demands, since a group is asked for exact numbers at a point of a border and
     * for the classes themselves where a class is what a row stands in.
     */
    sealed interface JointBuilder {

        Realization from(Type sourceType, SequencedMap<RealizationTarget, AskedAt> demands,
                         Quantities measuring, SearchRegion within, RuleReadingContext reading);

        /**
         * One number, whose value is what every other reader of this file asks for.
         *
         * <p>Here so that a group of one is not a second way of doing what
         * {@link TermRealizations#satisfying(Type, TermOrders, NumericSet, SearchRegion,
         * RuleReadingContext)} does — it is that way, reached by the one road a caller takes to any
         * group.
         */
        record OneNumberOnItsOwn() implements JointBuilder {

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                Map.Entry<RealizationTarget, AskedAt> one = demands.firstEntry();
                return satisfying(sourceType, measuring.ordersOf(one.getKey().term()),
                        one.getValue(), within, reading);
            }
        }

        /** The parts of a time, each standing at what its own set admits. */
        record AtThoseTimeParts(SequencedMap<RealizationTarget, TakenAs.TimePart> parts)
                implements JointBuilder {

            public AtThoseTimeParts {
                if (parts.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a way of writing a value for some parts says which parts");
                }
                parts = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(parts));
            }

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                Map<TakenAs.TimePart, NumericSet> asked = new LinkedHashMap<>();
                for (Map.Entry<RealizationTarget, TakenAs.TimePart> each : parts.entrySet()) {
                    asked.put(each.getValue(), demands.get(each.getKey()).walking());
                }
                return atThoseParts(asked, sourceType, rootOf(parts.keySet(), measuring),
                        reading.source());
            }
        }

        /** The parts of a date, solved over the calendar. */
        record OnThoseDateParts(SequencedMap<RealizationTarget, TakenAs.DatePart> parts)
                implements JointBuilder {

            public OnThoseDateParts {
                if (parts.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a way of writing a value for some parts says which parts");
                }
                parts = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(parts));
            }

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                Map<TakenAs.DatePart, NumericSet> asked = new LinkedHashMap<>();
                for (Map.Entry<RealizationTarget, TakenAs.DatePart> each : parts.entrySet()) {
                    asked.put(each.getValue(), demands.get(each.getKey()).walking());
                }
                return onThoseParts(asked, sourceType, rootOf(parts.keySet(), measuring),
                        reading.source());
            }
        }

        /**
         * One number of the place whose quotients are the numbers asked for, solved out of them.
         *
         * <p><b>Solved and not put together.</b> A quotient is no place in the spelling of a
         * number, so there is nothing to write side by side: what a value of the place may be is
         * every demand's answer at once, and finding one is looking in the run they leave between
         * them. Which the account can say because a quotient by a written number runs over a run
         * of the place — the numbers whose half is five are ten and eleven — so each demand is a
         * pair of ends and the demands together are their meet.
         *
         * <p><b>What the walk reached is what it says, and no more.</b> Where both ends are written
         * down this walks every whole number the demands leave between them, so a run with nothing
         * in it is a run this had the whole of — and it is still not a sentence about the model,
         * because what the demands were is a class the rules left or one value a caller picked and
         * nothing here can tell those apart ({@link Realization.None}). Where an end is open the
         * carrier names one place instead and what comes back says which population that was one
         * of.
         */
        record SolvingForTheirQuotients(SequencedMap<RealizationTarget, BigDecimal> by)
                implements JointBuilder {

            public SolvingForTheirQuotients {
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a solving for some quotients says which divisors they are by");
                }
                by = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(by));
            }

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                Carrier observed = rootOf(by.keySet(), measuring);
                if (observed == null) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                NumericDomain.Bounds lies = NumericDomain.Bounds.OPEN;
                for (Map.Entry<RealizationTarget, BigDecimal> each : by.entrySet()) {
                    NumericDomain.Bounds quotients =
                            quotientsAsked(demands.get(each.getKey()).walking());
                    if (quotients == null) {
                        return new Realization.Unexhausted(Set.of(CompositionRepertoire
                                .VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS), null);
                    }
                    // And what the rules leave the quotient room for, which is about the way to
                    // the point rather than about this demand. A region that leaves the number
                    // nowhere is a thing the rules say, so the run is empty and this says nothing
                    // was built in it.
                    switch (within == null ? null
                            : within.projectionOf(each.getKey().term())) {
                        case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                                quotients = quotients.meet(held);
                        case NumericDomain.FormProjection.NothingIsLeft _ -> {
                            return new Realization.None(
                                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                        }
                        case null -> { }
                    }
                    lies = lies.meet(numbersWhoseQuotientLiesIn(quotients, each.getValue()));
                }
                RuleReadingSource ruleSource = reading.source();
                return firstThatBuilds(walkIsOfTheWholeQuestion(demands.values()),
                        numbersInside(lies, observed,
                                at -> readsBackIntoEveryOne(at, by, demands, observed)),
                        at -> writtenAt(at, sourceType, observed, ruleSource));
            }
        }

        /**
         * The value the place is asked to stand at, with the numbers taken of it read off it.
         *
         * <p><b>Offered and read back, not solved for.</b> A group asking what stands at a place
         * and asking for a number taken of what stands there asks one question about one value:
         * the place's own demand says which values may stand there, and a number taken of one of
         * them is what reading that value comes to. So what to try is that demand's to say, and
         * every other number of the group is a question asked of each of them.
         *
         * <p><b>Which leaves the quantifier where the value's demand put it.</b> A demand naming
         * one value hands over that value and has nothing else to hand over; a demand leaving a run
         * of them hands over the place a carrier names inside it, and nothing built at that one
         * says which population it was one of. Either way what a walk reached is as far as it was
         * going to go: what a set of one value is a set of is a question nothing here can ask
         * ({@link Realization.None}), so a value refused by a number taken of it is not read back
         * as a class the rules leave nothing at.
         */
        record ItsOwnValueAndWhatIsTakenOfIt(RealizationTarget itself,
                                            List<RealizationTarget> takenOfIt)
                implements JointBuilder {

            public ItsOwnValueAndWhatIsTakenOfIt {
                if (takenOfIt.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a value offered for the numbers taken of it says which numbers those"
                                    + " are");
                }
                takenOfIt = List.copyOf(takenOfIt);
            }

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                TermOrders orders = measuring.ordersOf(itself.term());
                AskedAt standsAt = demands.get(itself);
                NumericSet stands = standsAt == null ? null : standsAt.walking();
                if (orders == null || orders.observed() == null || orders.answered() == null
                        || stands == null) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                // What each of the taken numbers is asked, put together before a value is tried.
                // Everything here is about the place and the way to the point, so a walk that
                // worked it out per candidate would ask the same questions again at every value
                // and answer them the same way.
                List<Asked> readOfEach = new ArrayList<>();
                for (RealizationTarget each : takenOfIt) {
                    TermOrders of = measuring.ordersOf(each.term());
                    AskedAt at = demands.get(each);
                    NumericSet wanted = at == null ? null : at.walking();
                    if (of == null || of.answered() == null || wanted == null) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    // And where the rules leave the number on the way, which is exhaustive over
                    // what a region answers: a region admitting no assignment leaves its number
                    // nowhere, which is a thing the rules say and not a value of the place failing
                    // to read back as one.
                    switch (within == null ? null : within.projectionOf(each.term())) {
                        case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                                readOfEach.add(new Asked(of, wanted, held));
                        case NumericDomain.FormProjection.NothingIsLeft _ -> {
                            return new Realization.None(Generator.UnresolvedCombination.Reason
                                    .NOTHING_COMPOSES_ONE);
                        }
                        // Nothing said about this number on the way, which leaves every value of
                        // it standing.
                        case null -> readOfEach.add(new Asked(of, wanted, null));
                    }
                }
                RuleReadingSource ruleSource = reading.source();
                Carrier answered = orders.answered();
                return firstThatBuilds(walkIsOfTheWholeQuestion(demands.values()),
                        admitting(onTheOrder(stands, orders, standsAt.named(), within),
                                at -> everyNumberTakenOfItReadsBack(at, orders.observed(),
                                        readOfEach)),
                        at -> writtenAt(at, sourceType, answered, ruleSource));
            }
        }

        /**
         * A container holding one of those many, whose elements come to one of those totals.
         *
         * <p><b>Composed out of both numbers, and read for neither.</b> How many a container holds
         * and what it comes to are no places in the spelling of one — a list is not written by
         * writing its length beside its total — and neither is read off a value the group already
         * asks for. What has both is built: a size the first number leaves, filled so that the
         * elements come to the second.
         *
         * <p><b>Which is the composing a total already does.</b> Filling a container to a total is
         * choosing how many elements it holds and what each of them holds, so the sizes are walked
         * there and a second number about the size is one more thing that says which sizes there
         * are — beside what the declarations leave the container and what the rules leave it on the
         * way. So this hands the size demand over rather than filtering what came back: a size the
         * demand refuses is no candidate, and a walk that filled one would spend a figure of this
         * compiler's on a container nobody asked for.
         */
        record HoldingThatManyAndAddingUpToThat(RealizationTarget manyItHolds,
                                                RealizationTarget whatItComesTo)
                implements JointBuilder {

            @Override
            public Realization from(Type sourceType,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading) {
                TermOrders counted = measuring.ordersOf(manyItHolds.term());
                TermOrders adds = measuring.ordersOf(whatItComesTo.term());
                AskedAt holdsAt = demands.get(manyItHolds);
                AskedAt comesToAt = demands.get(whatItComesTo);
                NumericSet many = holdsAt == null ? null : holdsAt.walking();
                NumericSet total = comesToAt == null ? null : comesToAt.walking();
                if (counted == null || counted.answered() == null || adds == null
                        || many == null || total == null) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                // Where the rules leave the size on the way, which the container's own walk asks
                // of the region already. What is handed over here is the group's demand and not
                // the way, so neither reading stands in for the other.
                if (within != null && within.projectionOf(manyItHolds.term())
                        instanceof NumericDomain.FormProjection.NothingIsLeft) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                ContainersAddingUp.HowManyIsAskedFor holding =
                        new ContainersAddingUp.HowManyIsAskedFor(many, counted.answered());
                return firstThatBuilds(walkIsOfTheWholeQuestion(demands.values()),
                        onTheOrder(total, adds, comesToAt.named(), within),
                        at -> ContainersAddingUp.to(at, sourceType, adds, within, reading,
                                holding));
            }
        }

        /**
         * The carrier the group's root is observed on, or null where a term of it is not measured.
         *
         * <p>One root has one, so this is read off each term and is the same answer every time
         * round — which is what being one location means. Read off the group rather than handed in
         * because a term measured somewhere else is a term whose value would be written on a
         * carrier a caller found elsewhere.
         */
        private static Carrier rootOf(Collection<RealizationTarget> group, Quantities measuring) {
            Carrier observed = null;
            for (RealizationTarget target : group) {
                TermOrders orders = measuring.ordersOf(target.term());
                if (orders == null) {
                    return null;
                }
                observed = orders.observed();
            }
            return observed;
        }
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
     * are, which is what {@link #jointRealizationOf} answers and this does not.
     *
     * <p><b>A group nothing writes a value for is said as the population it is part of.</b> That
     * nothing here writes a value for several numbers of one place is a fact about this compiler
     * and never one about the model: two totals of one container are both asked for by models that
     * have such a container in them, and a word for a walk that looked everywhere would tell their
     * author no value exists. Nothing looked. So what comes back is a walk that offered
     * none of a population, which is the answer a reader may conclude nothing from.
     */
    static Realization allSatisfying(Type sourceType,
                                     SequencedMap<RealizationTarget, AskedAt> demands,
                                     Quantities measuring,
                                     SearchRegion within,
                                     RuleReadingContext reading) {
        // What type the value is written at is the caller's answer and is settled before this is
        // asked. Read here as one more thing that could be missing, a location whose write path
        // this reading has no type for would come back as a group nothing solves — which is a
        // sentence about what this compiler cannot compose, said of a question nobody asked.
        assert sourceType != null : "a group is realized at the type its caller settled";
        return switch (jointRealizationOf(demands.keySet())) {
            // Which population, and no detail beside it: nothing was walked here, so there is
            // nothing this found to tell a reader.
            case JointRealization.Missing(CompositionRepertoire notAllOf) ->
                    new Realization.Unexhausted(Set.of(notAllOf), null);
            case JointRealization.Supported(JointBuilder builder) ->
                    builder.from(sourceType, demands, measuring, within, reading);
        };
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
                          Place answer, SearchRegion within,
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
                                  SearchRegion within,
                                  RuleReadingContext reading) {
        return satisfying(sourceType, orders, wanted, null, within, reading);
    }

    /**
     * The values to write at {@code orders}' root answering what this was asked, which says both
     * which numbers to walk and which numbers a walk of them is about.
     */
    static Realization satisfying(Type sourceType, TermOrders orders, AskedAt asked,
                                  SearchRegion within,
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
            case NumericTerm.ValueOf _ -> standing(sourceType, orders, asked, within, reading);
            case NumericTerm.TakenOf taken -> taken(taken.takenAs(), taken.arguments(), sourceType,
                    orders, asked, within, reading);
            case NumericTerm.TakenOver over -> overARun(over.takenAs(), sourceType, orders,
                    asked, within, reading);
        };
    }

    /**
     * The same, with a number of the set a caller has already named.
     *
     * <p><b>A candidate, and never the question.</b> What the search is asked for stays the set:
     * a number picked out of it is one this may try first, and its failing says nothing about the
     * numbers beside it. Handed in as the set instead — as the one number the set holds — a class
     * whose first candidate nothing builds at comes back as a class nothing writes a value in,
     * which is the quantifier this file exists to keep where it belongs.
     *
     * <p>For the sets this cannot walk: the numbers a rule leaves when it singles one out are every
     * number but those, and which of them to try is a witness somebody pays for. So the reader that
     * pays names one, and what comes of it is an answer about that one.
     */
    static Realization satisfying(Type sourceType, TermOrders orders, NumericSet wanted,
                                  Place named,
                                  SearchRegion within,
                                  RuleReadingContext reading) {
        return satisfying(sourceType, orders,
                AskedAt.aNumberOutOf(wanted, named, orders.answered()),
                within, reading);
    }

    /**
     * A value of the position itself standing at one of those numbers.
     *
     * <p>Chosen against the carrier and inside what the rules leave, which is the search a class of
     * such a position is cut by and is asked here the same way. The order's own ends come from the
     * region, since where a row may be written is what says how far the values run — worked out
     * from the type instead, this would answer about wherever that type came from.
     */
    private static Realization standing(Type sourceType, TermOrders orders, AskedAt asked,
                                        SearchRegion within,
                                        RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        Carrier carrier = orders.answered();
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                onTheOrder(asked.walking(), orders, asked.named(), within),
                chosen -> oneValue(
                        FixtureTemplate.on(carrier, chosen, ruleSource.symbols().scope()::reach),
                        sourceType, ruleSource));
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
                                     TermOrders orders, AskedAt asked,
                                     SearchRegion within,
                                     RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        NumericSet wanted = asked.walking();
        return switch (how) {
            // A container has no order of its own and is built out of what it holds, so this arm
            // takes none. That is the arm's own answer and not an order standing in for nothing.
            case TakenAs.HowManyItHolds _ -> holding(sourceType, asked, orders, reading);
            // A container whose elements come to the total, which is what a row has to hold for
            // this number to be there. What that takes is choosing how many elements and what each
            // of them holds — one question whether the number is added up out of the container
            // itself or out of a path inside its elements, and answered for both in one place.
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(asked, sourceType, orders,
                    within, reading);
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
                    atThatQuotient(taken.read(arguments), sourceType, orders, asked,
                            within, ruleSource);
        };
    }

    /**
     * Whether walking what each of these hands over is walking what they are about.
     *
     * <p>Of all of them, because one value answers the group and a word about it is a word about
     * every number the group asked for. One of them a caller picked a number out of is one the
     * walk saw a candidate of, and the answer is about that candidate whatever the rest were
     * asked.
     */
    private static boolean walkIsOfTheWholeQuestion(Collection<AskedAt> asked) {
        return asked.stream().allMatch(AskedAt::walkIsOfTheWholeQuestion);
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
     *
     * <p><b>And all the numbers handed over is not all the numbers asked about.</b> What handed
     * them over says which of its own it had left, and that is a walk's answer rather than a
     * question's: the numbers handed over are the ones a caller named where a caller named any. So
     * the one place a walk becomes something said about the model is here, and what it is said of
     * is what the search was for.
     */
    private static Realization firstThatBuilds(boolean walkedTheWholeQuestion, Tried tried,
                                               Function<Place, Realization> of) {
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
                // The rules leaving no number at one of the numbers handed over says nothing about
                // the next: this walk is over the numbers, and that one was a value's answer.
                case Realization.NoNumberTheRulesAdmit _, Realization.None _,
                     Realization.Built _ -> { }
            }
        }
        // Why there were no more to try, said by whatever handed them over. Worked out here, this
        // would be the one place that knows what every account's numbers are and how it walks them,
        // which is what handing the reason over is for.
        switch (tried.rest()) {
            case Remainder.Exhausted _ -> { }
            case Remainder.StoppedAt(CompositionBudget figure) -> met.add(figure);
            case Remainder.SomeOf(Set<CompositionRepertoire> written) -> some.addAll(written);
        }
        if (!met.isEmpty()) {
            return new Realization.Stopped(met, some);
        }
        if (!some.isEmpty()) {
            return new Realization.Unexhausted(some,
                    last instanceof Realization.Unexhausted walked ? walked.detail() : null);
        }
        // Nothing was handed over, nothing was held back, and the numbers there were to hand over
        // were the whole of what was asked about. Which is the rules admitting no number of the
        // question, and the one answer here that is about the model rather than about this
        // compiler.
        //
        // Both halves are the point. A walk over a number a caller picked out of a class ends the
        // same way and has seen one number of it, so the same emptiness said of the class would be
        // a sentence about every value the class holds. And nothing here says anything about what
        // could be built at a number this walked past: this is about the numbers, not the values.
        if (tried.numbers().isEmpty() && tried.rest() instanceof Remainder.Exhausted
                && walkedTheWholeQuestion) {
            return new Realization.NoNumberTheRulesAdmit();
        }
        return last instanceof Realization.None none ? none
                : new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }

    /** A container whose elements come to one of those numbers, which is what a row has to hold for
     *  this number to be there. */
    private static Realization addingUp(AskedAt asked, Type sourceType, TermOrders orders,
                                        SearchRegion within,
                                        RuleReadingContext reading) {
        if (orders.answered() == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // A total is a place on the order it is measured on and not a count of anything, so what
        // there is to try is what that order has in the run — which is the carrier's answer and
        // covers the totals a decimal reaches between two whole numbers.
        //
        // Asked on the order the total is measured on, which a run of values answers a number over
        // and stands at no place of. Read on the order the values are written on instead, a total
        // taken over a run would be asked about a carrier the run has and the number does not.
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                onTheOrder(asked.walking(), orders, asked.named(), within),
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
    private static Realization atThatQuotient(BigDecimal by, Type sourceType, TermOrders orders,
                                              AskedAt asked,
                                              SearchRegion within,
                                              RuleReadingSource ruleSource) {
        Carrier observed = orders.observed();
        // A divisor that is not there, or is nought, is a term nothing built — what quotients there
        // are is settled where the account is asked for. Answered here as a place nothing composes
        // a value for, which is what a reader that got this far has somewhere to put.
        if (observed == null || by == null || by.signum() == 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // A quotient is a place on the order it is answered on, and how far that order runs is the
        // carrier's. Walked as whole numbers between figures of this compiler's instead, a quotient
        // the position holds and an int does not was a number nothing offered.
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                onTheOrder(asked.walking(), orders, asked.named(), within),
                quotient -> multipliedBack(by, sourceType, observed, quotient, ruleSource));
    }

    /**
     * The numbers a search was handed, and why there are no others.
     *
     * <p>Both from whoever handed them over. A walk that filled what it was allowed and a walk that
     * ran out of numbers hand back the same list, and only the walk knows which it was — so the
     * reason travels beside them rather than being read off how many there are.
     *
     * @param numbers what to try, in the order to try them
     * @param rest    why there are no more, which is what tells a set with no value in it from a
     *                search that stopped short of one
     */
    private record Tried(List<Place> numbers, Remainder rest) {

        static Tried allOf(List<Place> numbers) {
            return new Tried(numbers, new Remainder.Exhausted());
        }

        /** The one number a set of one is, handed over without a window: what an account can be
         *  asked for is the account's to judge, and a demand for one number names it outright. */
        static Tried theOne(Place number) {
            return allOf(List.of(number));
        }
    }

    /**
     * Why there are no more numbers to try than the ones handed over.
     *
     * <p><b>The producer's answer, and the reason a consumer does not have to guess one.</b> Three
     * things leave a search with numbers it did not try, and they are three different things to
     * tell an author: the set had no more, a figure of this compiler's stopped the handing over,
     * or this compiler has one way of naming a number where the set has many. Carried as whether
     * the set was exhausted, the last two are one bit — and what a reader was told is the figure,
     * which they may raise to be handed exactly what they were handed before.
     *
     * <p>The same three {@link Realization} is told apart by, one step earlier. A search that says
     * why it stopped and a set of candidates that does not would leave the word a reader gets
     * standing on a guess.
     */
    private sealed interface Remainder {

        /** There are no more: the numbers handed over are every one the set has in the window its
         *  account can be asked for. */
        record Exhausted() implements Remainder {}

        /** A figure of this compiler's stopped the handing over, and raising it hands over more. */
        record StoppedAt(CompositionBudget figure) implements Remainder {}

        /** This compiler writes some of the numbers there are and has no way of writing the rest,
         *  which no figure reaches. */
        record SomeOf(Set<CompositionRepertoire> written) implements Remainder {

            public SomeOf {
                written = Set.copyOf(written);
                if (written.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a walk that wrote some of them says some of what");
                }
            }
        }
    }

    /**
     * The whole numbers of a set between two of them, in the order to try them.
     *
     * <p>For the accounts whose numbers are whole and whose window is their own: how many a
     * container holds, a part of a time, a part of a date. The window is the caller's because what
     * a number of that kind can be at all is what the caller knows, and what comes back says
     * whether the window ran out or the figure did.
     */
    private static Tried wholeNumbers(NumericSet wanted, Carrier on, long from, long to,
                                      int many) {
        return wholeNumbers(wanted.extent(), at -> wanted.holds(at, on),
                BigDecimal.valueOf(from), BigDecimal.valueOf(to), many);
    }

    /**
     * The same, of ends and a membership a caller answers rather than of one set.
     *
     * <p>For a number several sets are asked of at once: which numbers a value of the place may be
     * is every set's answer together, and no one of them is the question. The ends narrow the
     * walking and the membership decides it, which is the arrangement the single set has as well —
     * {@link NumericSet#extent()} beside {@link NumericSet#holds}.
     */
    private static Tried wholeNumbers(NumericDomain.Bounds lies, Predicate<Place> holds,
                                      BigDecimal from, BigDecimal to, int many) {
        // Narrowed to where the set lies before a step is taken. The window is as wide as the kind
        // of number goes, and stepping through the part of it the set is nowhere near is a walk
        // over the kind rather than a choice between the numbers the rules admit.
        BigDecimal first = startOf(lies.min(), from);
        BigDecimal last = endOf(lies.max(), to);
        List<Place> out = new ArrayList<>();
        // One past what is handed over, so that a window holding exactly as many as the figure
        // allows is a window this walked to the end of. Stopped at the figure itself, a set of
        // exactly that many numbers comes back as a search that gave something up.
        for (BigDecimal at = first; at.compareTo(last) <= 0 && out.size() <= many;
                at = at.add(BigDecimal.ONE)) {
            Count place = new Count(at);
            if (holds.test(place)) {
                out.add(place);
            }
        }
        return out.size() > many
                ? new Tried(List.copyOf(out.subList(0, many)),
                        new Remainder.StoppedAt(CompositionBudget.NUMBERS_OF_A_SET_TRIED))
                : Tried.allOf(List.copyOf(out));
    }

    /** The first whole number at or above an end, or the window's own start where the set runs
     *  past it. */
    private static BigDecimal startOf(Endpoint end, BigDecimal from) {
        if (end == null || !(end.at() instanceof Count count)) {
            return from;
        }
        BigDecimal edge = count.at().setScale(0, java.math.RoundingMode.CEILING);
        return from.max(!end.inclusive() && edge.compareTo(count.at()) == 0
                ? edge.add(BigDecimal.ONE) : edge);
    }

    /** The last whole number at or below an end, or the window's own end where the set runs past
     *  it. */
    private static BigDecimal endOf(Endpoint end, BigDecimal to) {
        if (end == null || !(end.at() instanceof Count count)) {
            return to;
        }
        BigDecimal edge = count.at().setScale(0, java.math.RoundingMode.FLOOR);
        return to.min(!end.inclusive() && edge.compareTo(count.at()) == 0
                ? edge.subtract(BigDecimal.ONE) : edge);
    }

    /**
     * A number of a set on the order its values are counted on, asked of the carrier.
     *
     * <p>For the accounts whose numbers are a place on an order rather than a count of something:
     * what a position itself stands at, what a run of values comes to, what a division answers. How
     * those values step is the carrier's one answer and covers the orders that are dense as well as
     * the ones that are not — worked out here as whole numbers, a run between a tenth and nine
     * tenths would hold none, and a number past what an int holds would be one nothing offers.
     *
     * <p>One of them, and what comes back says so — as a population this compiler writes some of
     * and never as a figure. Raising a number reaches no second place in a run: where the order has
     * a smallest step nothing here steps to it, and where it has none there is no step. So a caller
     * that built nothing at the one place has not walked the run, and what it may say is that, and
     * not that the run holds nothing.
     */
    private static Tried onTheOrder(NumericSet wanted, TermOrders orders, Place named,
                                    SearchRegion within) {
        if (wanted instanceof NumericSet.At one) {
            // A set of one number is that number, and there is nothing else it could have been.
            return Tried.theOne(one.value());
        }
        Set<CompositionRepertoire> ofTheRun =
                Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED);
        if (!(wanted instanceof NumericSet.InARun run)) {
            // Anything but the values a rule singled out. Which place beside them to try is a
            // witness somebody pays for, and what a witness may cost is named where witnesses are
            // paid for — so a caller that paid names one and this tries it. Nothing built at it is
            // an answer about that number: the set holds every other one, and none was looked at.
            return new Tried(named == null ? List.of() : List.of(named),
                    new Remainder.SomeOf(ofTheRun));
        }
        // Where the rules leave the number room, which narrows the run this looks in. Exhaustive
        // over what the region answers, because one of its answers is not a range: a region that
        // admits no assignment leaves the number nowhere, and read back as a pair of open ends it
        // would be the widest answer there is out of the narrowest region there is.
        NumericDomain.Bounds leaves;
        switch (within == null ? null : within.projectionOf(orders.term())) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) -> leaves = held;
            // The rules leave nowhere to write, which is a thing they say and not a walk of this
            // compiler's giving up. So the candidates are none and the reason is that there were
            // none — the same reading every other search of a region takes.
            case NumericDomain.FormProjection.NothingIsLeft _ -> {
                return new Tried(List.of(), new Remainder.Exhausted());
            }
            case null -> leaves = null;
        }
        Place found = new Criterion.Within(run.run(), null, Towards.ABOVE).somewhereInside(
                orders.answered(),
                leaves == null ? null : leaves.min(), leaves == null ? null : leaves.max());
        return new Tried(found == null ? List.of() : List.of(found),
                new Remainder.SomeOf(ofTheRun));
    }

    /**
     * The quotients a set asks for, as ends, or null where the set is not a run of them.
     *
     * <p>Every number but the ones a rule singled out is an order with holes in it, and no pair of
     * ends is that. Which is a population nothing here solves a value out of rather than a set
     * with nothing in it, so a caller says that and does not read these ends as open.
     */
    private static NumericDomain.Bounds quotientsAsked(NumericSet wanted) {
        return switch (wanted) {
            case NumericSet.At one -> new NumericDomain.Bounds(
                    Endpoint.inclusive(one.value()), Endpoint.inclusive(one.value()));
            case NumericSet.InARun _ -> wanted.extent();
            case NumericSet.AwayFrom _ -> null;
        };
    }

    /**
     * The numbers of a place whose quotient by {@code by} lies between {@code quotients}.
     *
     * <p><b>Exactly that run.</b> Truncation is not a bijection: a run of numbers answers each
     * quotient, so a run of quotients is a run of the place — ten and eleven are the numbers whose
     * half is five. Every number these ends hold has its quotient between the ones asked for, and
     * every number that does is between them.
     *
     * <p>Which the walk over them rests on. A figure of this compiler's counts the numbers a walk
     * admits, so a pair of ends holding numbers the demands turn down is a walk that steps without
     * spending anything — and the numbers between an end and the truth are as many as the divisor
     * is wide. Read as one quotient further out for the sake of a simpler reading of exclusivity,
     * a model whose divisor is a billion would step through billions of them.
     *
     * <p>The membership is asked all the same, and not as a repair of this: what a builder owes is
     * that the value it writes reads back as the number it was asked for, and reading it back is
     * the only thing that says so.
     */
    static NumericDomain.Bounds numbersWhoseQuotientLiesIn(NumericDomain.Bounds quotients,
                                                           BigDecimal by) {
        // Dividing by a negative counts the other way, so the ends swap: the numbers whose
        // quotient by minus two is at least three are the ones whose quotient by two is at most
        // minus three. Answered by turning the ends round rather than by a second set of cases.
        BigDecimal size = by.abs();
        Endpoint low = by.signum() > 0 ? quotients.min() : upsideDown(quotients.max());
        Endpoint high = by.signum() > 0 ? quotients.max() : upsideDown(quotients.min());
        return new NumericDomain.Bounds(
                low == null ? null : Endpoint.inclusive(lowestWhoseQuotientIs(low, size)),
                high == null ? null : Endpoint.inclusive(highestWhoseQuotientIs(high, size)));
    }

    /**
     * The whole numbers inside these ends that {@code holds} admits, in the order to try them, or
     * the one place the carrier names where the ends do not close.
     *
     * <p>Stepped where both ends are written down. The ends are exactly the run the demands leave
     * ({@link #numbersWhoseQuotientLiesIn}), so every number stepped is one the demands admit and
     * the figure that counts them counts the work — a wide divisor makes the run wide and the
     * figure stops the walk in it, rather than leaving a walk that steps without spending.
     *
     * <p>Where an end is open there is nothing to step from, so the carrier names a place the way
     * it does for a run — and what comes back says this wrote one of them, since raising nothing
     * reaches a second.
     *
     * <p><b>Held to what the place can hold before a step is taken, and not after.</b> A number the
     * carrier does not reach is a number no row writes, so it is no candidate — and the figure
     * counts candidates. Left to the writing to turn down, the numbers a divisor as wide as the
     * order itself puts below the order's own end would take the whole figure, and the numbers the
     * place does hold would never be reached: an answer saying a figure of this compiler's stopped
     * it, of a place with a value in it, and a figure nobody can raise far enough to reach one.
     *
     * <p><b>And it bounds the walking without being said to the carrier.</b> What the demands leave
     * is what a place is named inside, and the ends of that are theirs: handed the order's own end
     * as though a rule had written it, a run open below is a run starting at the smallest whole
     * number there is, and every row for a number below something is written at it. So the ends a
     * place is named inside are the demands' and the window stepped through is the meet.
     */
    private static Tried numbersInside(NumericDomain.Bounds lies, Carrier on,
                                       Predicate<Place> holds) {
        OrderedInterval reaches = on.extent();
        NumericDomain.Bounds within =
                lies.meet(new NumericDomain.Bounds(reaches.low(), reaches.high()));
        if (lies.min() != null && lies.max() != null
                && within.min().at() instanceof Count low
                && within.max().at() instanceof Count high) {
            return wholeNumbers(within, holds, low.at(), high.at(),
                    CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum());
        }
        Place found = on.somethingInside(lies.min(), lies.max());
        return new Tried(found == null || !holds.test(found) ? List.of() : List.of(found),
                new Remainder.SomeOf(Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED)));
    }

    /**
     * Whether the quotient of {@code at} by each of those divisors is one of the numbers that
     * demand asked for.
     *
     * <p><b>Read through the account and not off the ends.</b> Which numbers a value answers is
     * what reading it comes to, so a candidate is admitted by dividing it and asking each set —
     * the ends above only say where to look. Decided from the ends instead, a number the
     * arithmetic put in the run and truncation does not would be a row offered at a number it
     * reads back as something else.
     */
    private static boolean readsBackIntoEveryOne(Place at,
                                                 SequencedMap<RealizationTarget, BigDecimal> by,
                                                 SequencedMap<RealizationTarget, AskedAt> asked,
                                                 Carrier observed) {
        if (!(at instanceof Count count)) {
            return false;
        }
        for (Map.Entry<RealizationTarget, BigDecimal> each : by.entrySet()) {
            AskedAt of = asked.get(each.getKey());
            NumericSet wanted = of == null ? null : of.walking();
            Place quotient = observed.onTheGrid(new Count(
                    Arithmetic.ATruncatingQuotient.quotientOf(count.at(), each.getValue())));
            if (wanted == null || quotient == null || !wanted.holds(quotient, observed)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The same numbers, less the ones a caller's question about each of them answers no to.
     *
     * <p><b>The reason there are no more is the walk's and is kept.</b> Whether the numbers handed
     * over were all there were is what handed them over, and a caller dropping some of them has
     * not learnt anything about that. Worked out here from how many are left, a walk that stopped
     * short and a walk that ran to the end would be told apart by a count of what this refused.
     *
     * <p>And every number dropped here was tried, so a figure counting what a walk hands over
     * still counts the work this does.
     */
    private static Tried admitting(Tried tried, Predicate<Place> holds) {
        List<Place> out = new ArrayList<>();
        for (Place at : tried.numbers()) {
            if (holds.test(at)) {
                out.add(at);
            }
        }
        return new Tried(List.copyOf(out), tried.rest());
    }

    /**
     * Whether a value standing at {@code at} reads back as one of the numbers asked for at each of
     * the numbers taken of it.
     *
     * <p><b>Read through the one reader.</b> Which number a taking answers of a value is what
     * reading that value comes to, so the value is put together and asked — the same walk down it
     * that a class of a row and a report take. Worked out here instead, this file would hold a
     * second account of what every operation answers, and the two would agree until one of them
     * was edited.
     *
     * <p>And what the rules leave the number on the way is asked beside the demand. A value whose
     * number is one the demand admits and the region does not is a value no row reaching the point
     * could stand at.
     *
     * <p>The place is asked of the carrier before it is made a value, because what a carrier can
     * hold is the carrier's answer: a count past the end of the order it stands on is no value of
     * it, and writing one out would be reading a place of some other carrier as one of these.
     */
    private static boolean everyNumberTakenOfItReadsBack(Place at, Carrier decoded,
                                                         List<Asked> readOfEach) {
        Place on = decoded.onTheGrid(at);
        if (on == null) {
            return false;
        }
        ObservedValue standing = decoded.valueOf(on);
        for (Asked each : readOfEach) {
            if (!(each.of().read(standing) instanceof NumericTerm.Reading.Number(Place number))
                    || !each.wanted().holds(number, each.of().answered())
                    || (each.leaves() != null && !each.leaves().admits(number))) {
                return false;
            }
        }
        return true;
    }

    /**
     * One of the numbers taken of a value, and everything asked of it that is not the value.
     *
     * @param of     the orders its number is read and measured on
     * @param wanted the numbers the rules leave it
     * @param leaves where the way to the point leaves it, or null where nothing on the way spoke
     *               of it
     */
    private record Asked(TermOrders of, NumericSet wanted, NumericDomain.Bounds leaves) { }

    /** An end of the quotients read on the other side of nought, which is what dividing by a
     *  negative number does to it. */
    private static Endpoint upsideDown(Endpoint end) {
        return end == null || !(end.at() instanceof Count count) ? null
                : new Endpoint(new Count(count.at().negate()), end.inclusive());
    }

    /**
     * The smallest number whose quotient by {@code size} is at or above that end, or null where
     * the end names no whole number.
     *
     * <p><b>The number itself and not one a whole quotient below it.</b> What a walk between two
     * of these steps is every number the ends hold, so an end further out than the truth is work
     * nobody asked for — and however wide a divisor is, the numbers between an end and the truth
     * are that many. The figure the walk holds to counts the numbers it admits, so it is no bound
     * on a walk that admits none of what it steps.
     *
     * <p>Which is why the quotient is read to the whole number the end admits first: the ends of a
     * run of quotients are read the way every walk of whole numbers here reads an end
     * ({@link #startOf}), and the run of the place is then exactly what those quotients answer.
     */
    private static Place lowestWhoseQuotientIs(Endpoint end, BigDecimal size) {
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        BigDecimal quotient = startOf(end, count.at());
        return new Count(quotient.signum() < 0
                ? quotient.multiply(size).subtract(size).add(BigDecimal.ONE)
                : quotient.signum() == 0 ? size.negate().add(BigDecimal.ONE)
                        : quotient.multiply(size));
    }

    /** The largest number whose quotient by {@code size} is at or below that end, read as exactly
     *  as the smallest is at the other. */
    private static Place highestWhoseQuotientIs(Endpoint end, BigDecimal size) {
        if (!(end.at() instanceof Count count)) {
            return null;
        }
        BigDecimal quotient = endOf(end, count.at());
        return new Count(quotient.signum() > 0
                ? quotient.multiply(size).add(size).subtract(BigDecimal.ONE)
                : quotient.signum() == 0 ? size.subtract(BigDecimal.ONE)
                        : quotient.multiply(size));
    }

    /** The one value whose quotient by that divisor is exactly that number. */
    private static Realization multipliedBack(BigDecimal by, Type sourceType, Carrier observed,
                                              Place answer, RuleReadingSource ruleSource) {
        if (!(answer instanceof Count wanted)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return writtenAt(new Count(wanted.at().multiply(by)), sourceType, observed, ruleSource);
    }

    /**
     * The value of a place standing at that number, wearing every name the place declares.
     *
     * <p>Where a number worked out for a root becomes a value, whichever reader worked it out: the
     * product a quotient asks for, the number several quotients leave. Past the end of what the
     * position's own order holds nothing is composed, and that is the carrier's answer rather than
     * anything counted here — a value past it is one no row can write however the arithmetic came
     * out.
     */
    private static Realization writtenAt(Place at, Type sourceType, Carrier observed,
                                         RuleReadingSource ruleSource) {
        Place on = observed.onTheGrid(at);
        if (on == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return oneValue(FixtureTemplate.on(observed, on, ruleSource.symbols().scope()::reach),
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
                                        TermOrders orders, AskedAt asked,
                                        SearchRegion within,
                                        RuleReadingContext reading) {
        return switch (how) {
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(asked, sourceType, orders,
                    within, reading);
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
    private static Realization holding(Type sourceType, AskedAt asked, TermOrders orders,
                                       RuleReadingContext reading) {
        // From none upward, which is as far as a count runs and as many of them as the figure
        // allows. A count is the one account whose numbers are whole and whose window is the whole
        // of what it can be asked for, so a walk that reaches the end of it has walked the set.
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                wholeNumbers(asked.walking(), orders.answered(), 0, Integer.MAX_VALUE,
                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum()),
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
        // composes one for rather than a value written without the name. Said with the name that
        // stopped it, and asked of the position rather than of the count, since it is the same
        // answer for every value ({@link #namesOf}).
        WornNames wears = namesOf(sourceType, ruleSource);
        if (!(wears instanceof WornNames.Spelled worn)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    ((WornNames.Unwritable) wears).why());
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
     * <p>At least one part, which both callers hold to: a group of them says which parts it is for
     * ({@link JointBuilder.AtThoseTimeParts}) and a single number is the part it is of.
     *
     * <p>The order is handed in and not named here. That what this is taken of is a time is the
     * arm's own condition and the library is held to it, but which carrier a time is written on is
     * {@link Carrier}'s one answer — named here, this would be a second place saying what a time
     * counts, and the two would part the day the first one moved.
     */
    private static Realization atThoseParts(Map<TakenAs.TimePart, NumericSet> parts,
                                            Type sourceType, Carrier observed,
                                            RuleReadingSource ruleSource) {
        if (observed == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        BigDecimal seconds = BigDecimal.ZERO;
        for (Map.Entry<TakenAs.TimePart, NumericSet> each : parts.entrySet()) {
            // The numbers this part runs between, which is what a value of it can be at all, and
            // the first of them the rules admit. Walked to the end, because a part is a handful of
            // numbers: a set that holds none of them is a set no time answers, which is a thing
            // this may say having looked at every one.
            List<Place> admitted = wholeNumbers(each.getValue(), observed,
                    0, each.getKey().many() - 1L, 1).numbers();
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
     * <p>At least one part, as the time above has: a group says which parts it is for
     * ({@link JointBuilder.OnThoseDateParts}) and a single number is the part it is of.
     *
     * <p>Whether a date can have the part at all is asked of the calendar and not of the bound the
     * operation declares. A bound is what the model may assume of an answer; what dates there are is
     * what a witness can be built from, and reading the second off the first would make a bound
     * loosened by hand into dates that cannot be written.
     */
    private static Realization onThoseParts(Map<TakenAs.DatePart, NumericSet> parts,
                                            Type sourceType, Carrier observed,
                                            RuleReadingSource ruleSource) {
        if (observed == null) {
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
                ? wholeNumbers(parts.get(TakenAs.DatePart.YEAR), observed,
                        java.time.LocalDate.MIN.getYear(), java.time.LocalDate.MAX.getYear(),
                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum())
                : Tried.allOf(List.of(Count.of(BigDecimal.valueOf(A_LEAP_YEAR))));
        List<Place> months = numbersOf(parts, TakenAs.DatePart.MONTH, observed,
                MONTHS_A_YEAR_HAS, A_LONGEST_MONTH);
        List<Place> days = numbersOf(parts, TakenAs.DatePart.DAY, observed,
                DAYS_THE_LONGEST_MONTH_HAS, FIRST_OF_THE_MONTH);
        boolean everyOne = years.rest() instanceof Remainder.Exhausted;
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
                : wholeNumbers(wanted, observed, 1, asFarAs, asFarAs).numbers();
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

    /**
     * One value, wearing every name the position declares, or the reason there is none.
     *
     * <p><b>Two reasons and not one.</b> A name this module cannot write is the same answer for
     * every value of the place and is said with the name that stopped it; nothing written down for
     * this number is about this number. Held as one branch — a value that came back null, whichever
     * of the two made it so — a walk asks the question about the place once per candidate and
     * spends a figure of this compiler's on it.
     */
    private static Realization oneValue(FixtureTemplate bare, Type sourceType, RuleReadingSource ruleSource) {
        if (namesOf(sourceType, ruleSource) instanceof WornNames.Unwritable cannot) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE, cannot.why());
        }
        if (bare == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return Realization.Built.whole(List.of(WornNames.under(
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.published()).wrappers(), bare, ruleSource)));
    }

    /**
     * How the names a place wears are written here, or the first of them that is not.
     *
     * <p><b>One place asks it of a place, because it is about the place.</b> The same answer holds
     * for every number and every value of it, so what a reader of this may not do is fold it in
     * with a value that was not built: a walk reading the two as one branch asks a question about
     * the place once per candidate and comes back saying a figure of this compiler's stopped it, of
     * a place where raising anything reaches nothing.
     *
     * <p>Nothing here asks it before a walk, because nothing gets this far with a name it cannot
     * write: what a class of the position is made of is refused first, and said there with the name
     * that stopped it ({@code PartitionClasses}).
     */
    private static WornNames namesOf(Type sourceType, RuleReadingSource ruleSource) {
        return WornNames.of(TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.published()).wrappers(), ruleSource);
    }

    private TermRealizations() {}
}
