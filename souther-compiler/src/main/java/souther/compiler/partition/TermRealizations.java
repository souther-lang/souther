package souther.compiler.partition;

import net.unit8.notation199x.pattern.CodePoints;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.ClassMembers;
import souther.compiler.check.HeldClass;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.ReadingsOfEachValue;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Congruences;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Today;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedRuns;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.UsualPlace;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.regex.Language;
import souther.compiler.values.ValueSet;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.SequencedMap;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.IntPredicate;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Stream;

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

    /**
     * What building values that answer a number came to.
     *
     * <p>What was not built is one {@link CompositionShortfall} wherever it travels, and never its
     * vocabularies taken apart. A caller holding a set per vocabulary carries on only the ones it
     * names, and a vocabulary it does not name is left out without anything saying so; one value
     * joined with {@link CompositionShortfall#and} carries every one.
     */
    sealed interface Realization {

        /** What of this compiler's this came to without, and {@link CompositionShortfall#NONE}
         *  where it is not a shortfall of this compiler's at all. */
        default CompositionShortfall shortfall() {
            return switch (this) {
                case Built built -> built.rest();
                case Stopped stopped -> stopped.met();
                case Unexhausted some -> some.met();
                case NoNumberTheDeclarationsAdmit _, None _ -> CompositionShortfall.NONE;
            };
        }

        /**
         * Values that answer it, and what was not built.
         *
         * <p>Two halves of one answer, as {@link Proposals} keeps them. A caller reading only
         * the first says every value was refused where some were never built, which is a different
         * thing to tell an author.
         *
         * <p><b>Everything the offer leaves out, and not only what a figure refused.</b> A walk that
         * went everywhere it knows how to go and a walk a figure turned back both leave values a
         * reader was not shown, and the reader deciding whether every value was refused needs the
         * two alike. Which of them a figure came to be here by is what {@link Stopped} is told
         * apart by, and it is not this.
         */
        record Built(List<FixtureTemplate> values, CompositionShortfall rest) implements Realization {

            public Built {
                values = List.copyOf(values);
                if (values.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a realization that built nothing is one that built none, and says why");
                }
            }

            static Built whole(List<FixtureTemplate> values) {
                return new Built(values, CompositionShortfall.NONE);
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
         * and is never a figure: it travels beside them in {@code met} where a figure was met as
         * well, and where none was it is {@link Unexhausted} rather than anything here.
         *
         * <p>Never where a value was built. A budget that cut an offering short after something was
         * composed is in {@link Built#rest()}: what it stopped is the rest of the offer, and the
         * point it was composed for has a value at it either way.
         */
        record Stopped(CompositionShortfall met) implements Realization {

            public Stopped {
                if (met.figures().isEmpty()) {
                    throw new IllegalArgumentException(
                            "a composing this compiler stopped says which budget stopped it");
                }
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
         * <p>What it met is a population walked in part, a number it could not hold, or both, and
         * never a figure: a figure met makes it {@link Stopped}.
         *
         * @param detail what this walk found, or null where it has nothing to add
         */
        record Unexhausted(CompositionShortfall met, String detail) implements Realization {

            public Unexhausted {
                if (!met.figures().isEmpty() || met.nothing()) {
                    throw new IllegalArgumentException(
                            "a walk that says it saw some of them, or could not hold a number on"
                                    + " the way, says which, and names no figure: " + met);
                }
            }
        }

        /**
         * The rules admit no number of what was asked about, which is walked and not guessed.
         *
         * <p><b>About the numbers and not about the values.</b> Nothing was built because there was
         * nothing to build for: the walk went over every number the question holds and the
         * declarations — the types and the rules written on them — left none of them standing. A walk that had numbers and built at none of them is not
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
         * a class one combination of leaves nothing would be a class the declarations leave
         * nothing in, while another combination of it goes on admitting values.
         */
        record NoNumberTheDeclarationsAdmit() implements Realization {}

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
         * {@link Generator.UnresolvedCombination.Reason#NO_VALUE_CAN_STAND_THERE}, and
         * nothing reaches it by counting what a walk refused.
         *
         * <p>The word is how a reader downstream treats it and {@code detail} is what happened in
         * this attempt, which is the arrangement {@link Generator.UnresolvedCombination} has between
         * its reason and what it said ({@link Generator.UnresolvedCombination#said()}). A
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
     * other is the calendar's, which {@link #dateAnsweringMovedParts} answers. A number whose values come of a run
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
        // How many elements meet a statement, which is answered by choosing elements and not by a
        // number standing anywhere. Every count of one container is one question about which
        // elements it holds, so they are composed together, with how many it holds beside them —
        // and so is a statement its elements meet together, which is answered the same way.
        List<RealizationTarget.ACount> counts = new ArrayList<>();
        List<RealizationTarget.ElementsMeetingTogether> together = new ArrayList<>();
        List<RealizationTarget.OfANumber> numbers = new ArrayList<>();
        for (RealizationTarget target : targets) {
            switch (target) {
                case RealizationTarget.ACount count -> counts.add(count);
                case RealizationTarget.ElementsMeetingTogether stated -> together.add(stated);
                case RealizationTarget.OfANumber number -> numbers.add(number);
            }
        }
        // What the elements of keys an input holds come to, with how many elements each key has
        // where that is counted beside it: the counts are the keys' own, which is a statement the
        // elements of a key meet by being its elements.
        List<RealizationTarget.OfANumber> totals = numbers.stream()
                .filter(each -> each.term() instanceof NumericTerm.GatheredUnderAKey).toList();
        if (together.isEmpty() && !totals.isEmpty()
                && (totals.size() > 1 || numbers.size() > 1 || !counts.isEmpty())
                && numbers.stream().allMatch(each -> totals.contains(each)
                        || standsAtTheKeyOfTheTotals(each, totals))
                && counts.stream().allMatch(count -> countsTheElementsOfAKeyOf(count, totals))) {
            return underSeveralKeys(targets, counts, totals, numbers);
        }
        if (!counts.isEmpty() || !together.isEmpty()) {
            return countsOf(targets, counts, together, numbers);
        }
        if (numbers.stream().anyMatch(each -> amongOneContainer(each.term()) != null)) {
            return amongTheElements(targets, numbers);
        }
        if (numbers.stream()
                .anyMatch(each -> each.term() instanceof NumericTerm.OccurrencesOfItsValue)) {
            return amongEveryOccurrence(targets, numbers);
        }
        if (numbers.stream()
                .anyMatch(each -> each.term() instanceof NumericTerm.OccurrencesOfAKey)) {
            return amongEveryOccurrenceEqualToAKey(targets, numbers);
        }
        if (targets.size() == 1 && numbers.getFirst().term() instanceof NumericTerm.TakenOver over
                && over.source() instanceof RunSource.SearchedLine) {
            return new JointRealization.Supported(
                    new JointBuilder.ALineToTheValue(numbers.getFirst()));
        }
        if (targets.size() == 1) {
            return new JointRealization.Supported(
                    new JointBuilder.OneNumberOnItsOwn(numbers.getFirst()));
        }
        SequencedMap<RealizationTarget.OfANumber, TakenAs.TimePart> times = new LinkedHashMap<>();
        SequencedMap<RealizationTarget.OfANumber, TakenAs.DatePart> dates = new LinkedHashMap<>();
        // What each part of a date was taken of, which is the date as it stands unless it was
        // moved first.
        SequencedMap<RealizationTarget.OfANumber, DateTranslation> moved = new LinkedHashMap<>();
        SequencedMap<RealizationTarget.OfANumber, BigDecimal> quotients = new LinkedHashMap<>();
        SequencedMap<RealizationTarget.OfANumber, BigDecimal> remainders = new LinkedHashMap<>();
        // What stands at the place, where the group asks for it as well as for numbers taken of
        // it. One group has at most one of these: what a number of a place is taken of is the
        // place, so a second value asked for is a second place and is another group's.
        RealizationTarget.OfANumber itself = null;
        List<RealizationTarget.OfANumber> takenOfIt = new ArrayList<>();
        // How many the container holds and what it comes to, which are the numbers a container
        // is composed out of rather than read for. It comes to as many totals as the group asks,
        // each of a field of its elements.
        RealizationTarget.OfANumber manyItHolds = null;
        List<RealizationTarget.OfANumber> whatItComesTo = new ArrayList<>();
        // How many of a string's code points are in a class and what they come to, which are
        // numbers of one string to be written together with how long it is.
        List<RealizationTarget.OfANumber> ofItsCodePoints = new ArrayList<>();
        // Every target read before any of them is answered, because what the group is turns on all
        // of them. Decided as they come, a value asked for beside a length would be the group the
        // length is in or the group the value is in depending on which of them was read first.
        for (RealizationTarget.OfANumber target : numbers) {
            switch (target.term()) {
                // Composed with the elements around it, which the arm above has already taken.
                case NumericTerm.Multiplicity _, NumericTerm.OccurrencesOfItsValue _,
                     NumericTerm.OccurrencesOfAKey _ -> {
                    return nothingSolvesAGroup();
                }
                // Written as the value it is the end of, alone: beside another number of the same
                // place it would be two numbers asked of one value that need not be one. The same
                // for what the elements of a key come to.
                case NumericTerm.ExtremeOfItsKey _, NumericTerm.GatheredUnderItsKey _,
                     NumericTerm.GatheredUnderAKey _ -> {
                    return nothingSolvesAGroup();
                }
                // Replaced by the numbers its two forms are of before a row is composed
                // ({@code Generator}), so it is never a number of a group.
                case NumericTerm.ProductOf _ -> {
                    return nothingSolvesAGroup();
                }
                // A number read off a value the group asks for, as any number taken of the place is:
                // the step a value falls in is what reading that value comes to. Asked beside the
                // value itself, the candidates are the value's and the step is read off each of
                // them; asked with no value beside it, nothing below writes one for it.
                case NumericTerm.WholeUnitsOf _ -> takenOfIt.add(target);
                case NumericTerm.ValueOf _ -> itself = target;
                // Numbers of a string, which a string is chosen for and no container is built to
                // have: what its code points come to is no total of elements composed one by one.
                case NumericTerm.CodePointClassCount _, NumericTerm.CodePointValueSum _,
                     NumericTerm.CodePointAt _ -> {
                    takenOfIt.add(target);
                    ofItsCodePoints.add(target);
                }
                // A number taken over the values a walk came to is a number of a run, and a value
                // standing at one place is not a run — so there is nothing here to read it off.
                // What is added up over a run is still a number the container it runs through is
                // composed to have, though, and that is the arm below.
                case NumericTerm.TakenOver over -> {
                    if (!(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)) {
                        return nothingSolvesAGroup();
                    }
                    whatItComesTo.add(target);
                }
                case NumericTerm.TakenOf taken -> {
                    takenOfIt.add(target);
                    switch (taken.takenAs()) {
                        case TakenAs.PartOfTime part -> times.put(target, part.part());
                        case TakenAs.PartOfDate part -> {
                            dates.put(target, part.part());
                            moved.put(target, taken.transformation().translation());
                        }
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
                        // A remainder is no place in the spelling of a number either. Asked for
                        // beside the place's own value it is read off each value offered; asked for
                        // alone, or beside remainders by other divisors, it is solved for below.
                        case TakenAs.TheFloorRemainder by -> {
                            BigDecimal divisor = by.read(taken.arguments());
                            if (divisor == null || divisor.signum() == 0) {
                                return nothingSolvesAGroup();
                            }
                            remainders.put(target, divisor);
                        }
                        // How much a container holds, which is what a container is composed out of
                        // rather than a place in the spelling of one: what answers a length and a
                        // total together is a container built to have both, and the arm below is
                        // where the two meet.
                        case TakenAs.HowManyItHolds _ -> manyItHolds = target;
                        case TakenAs.TheSumOfWhatItHolds _ -> whatItComesTo.add(target);
                    }
                }
            }
        }
        // The place's own value beside numbers taken of it, which is one question about one value.
        // What may stand there is what the place's own demand admits, and a number taken of one of
        // those values is what reading that value comes to — so the candidates are that demand's
        // and the rest of the group is read off each of them.
        if (itself != null) {
            RealizationTarget.OfANumber stands = itself;
            List<RealizationTarget> owned = new ArrayList<>(takenOfIt);
            owned.add(stands);
            return wholly(targets, owned,
                    () -> new JointBuilder.ItsOwnValueAndWhatIsTakenOfIt(stands, takenOfIt));
        }
        // Numbers of a string's code points, beside how long it is where that is asked: one string
        // written for all of them. Beside anything else of the place there is nothing here that
        // writes one, which is a capability this compiler lacks and not a string no numbers have.
        // Asked before a length meets a total, since a length beside what code points come to is
        // a string's two numbers and not a container's.
        if (!ofItsCodePoints.isEmpty()) {
            RealizationTarget.OfANumber length = manyItHolds;
            return wholly(targets, length == null ? ofItsCodePoints
                            : Stream.concat(ofItsCodePoints.stream(), Stream.of(length)).toList(),
                    () -> new JointBuilder.StringsHoldingTheirNumbers(ofItsCodePoints, length));
        }
        // How many a container holds beside what it comes to, which is one container to compose:
        // the sizes it may be are the ones the first number leaves, and filling one of those to
        // the second is what a total is composed by anyway. So is a container asked for more than
        // one total, which is one container whose elements hold a figure at each field a total
        // reads: a total of each is a share of every element, chosen together.
        if (!whatItComesTo.isEmpty() && (manyItHolds != null || whatItComesTo.size() > 1)) {
            if (whatItComesTo.size() > 1 && !ContainersAddingUp.addUpTogether(whatItComesTo)) {
                return nothingSolvesAGroup();
            }
            RealizationTarget.OfANumber many = manyItHolds;
            List<RealizationTarget.OfANumber> owned = new ArrayList<>(whatItComesTo);
            if (many != null) {
                owned.add(many);
            }
            return wholly(targets, owned,
                    () -> new JointBuilder.TotalsOfOneContainer(whatItComesTo, many));
        }
        // The remainders of one place by their divisors, with nothing else asked of it. A value
        // that is none of them is nothing these write, so a quotient or a part beside them is a
        // group nothing here solves.
        if (!remainders.isEmpty()) {
            if (!quotients.isEmpty() || !times.isEmpty() || !dates.isEmpty()
                    || manyItHolds != null || !whatItComesTo.isEmpty()) {
                return nothingSolvesAGroup();
            }
            return wholly(targets, remainders.keySet(),
                    () -> new JointBuilder.SolvingForTheirRemainders(remainders));
        }
        // A quotient of a place beside a part of it is a value that is both a number and a moment,
        // and what would write one is neither arm here.
        if (!quotients.isEmpty()) {
            return wholly(targets, quotients.keySet(),
                    () -> new JointBuilder.SolvingForTheirQuotients(quotients));
        }
        // Two asks at one part of a time, or at one part of a date moved by one translation, are
        // two asks for one number and are the same target, so a group holding one twice is a group
        // somebody built by hand — not a population this compiler writes none of. A part of a date
        // moved two ways is two numbers: the year of a date and the year of the day before it.
        assert Set.copyOf(times.values()).size() == times.size()
                && dates.keySet().stream().map(each -> List.of(dates.get(each), moved.get(each)))
                        .distinct().count() == dates.size()
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
        // The parts of a date, each after the date was moved as its own number says, where a date
        // that is not moved is one moved by nothing: every part asked is a condition on the days
        // the date comes from, so the group is one search over the days.
        return wholly(targets, times.isEmpty() ? dates.keySet() : times.keySet(),
                () -> times.isEmpty() ? new JointBuilder.OnThoseDateParts(dates, moved)
                        : new JointBuilder.AtThoseTimeParts(times));
    }

    /**
     * How often the value of an element occurs among the elements of one container — every one,
     * or those a statement keeps — with how many the container holds where the group asks that
     * too.
     *
     * <p>One container and one number of it. How often is asked of one place inside the element, so
     * two places are two questions about which elements are alike, and counts of the same
     * container beside them are a container composed for what the elements answer and for which of
     * them are alike together, which nothing here writes.
     */
    private static JointRealization amongTheElements(Collection<RealizationTarget> group,
                                                     List<RealizationTarget.OfANumber> numbers) {
        List<RealizationTarget.OfANumber> alike = new ArrayList<>();
        RealizationTarget.OfANumber many = null;
        for (RealizationTarget.OfANumber each : numbers) {
            if (amongOneContainer(each.term()) != null) {
                alike.add(each);
                continue;
            }
            if (!(each.term() instanceof NumericTerm.TakenOf taken)
                    || !(taken.takenAs() instanceof TakenAs.HowManyItHolds) || many != null) {
                return nothingSolvesAGroup();
            }
            many = each;
        }
        NumericTerm first = alike.getFirst().term();
        for (RealizationTarget.OfANumber each : alike) {
            if (!each.term().equals(first)) {
                return nothingSolvesAGroup();
            }
        }
        if (many != null && !((NumericTerm.TakenOf) many.term()).position()
                .equals(amongOneContainer(first))) {
            return nothingSolvesAGroup();
        }
        RealizationTarget.OfANumber holding = many;
        return wholly(group, Stream.concat(alike.stream(),
                        holding == null ? Stream.<RealizationTarget.OfANumber>empty()
                                : Stream.of(holding)).toList(),
                () -> new JointBuilder.ElementsAlikeAsOftenAsAsked(alike.getFirst(), holding));
    }

    /**
     * The container among whose elements {@code term} counts how often an element's value occurs,
     * where it is one container — of every element, or of those a statement keeps — or null where
     * it is no such number.
     */
    private static TermPath amongOneContainer(NumericTerm term) {
        return switch (term) {
            case NumericTerm.Multiplicity often -> often.container();
            case NumericTerm.OccurrencesOfItsValue often -> {
                List<TermPath> chain = often.subjectPath().containersHoldingIt();
                yield chain.size() == 1 ? chain.getFirst() : null;
            }
            case NumericTerm.FromOnePosition _, NumericTerm.TakenOver _,
                 NumericTerm.ExtremeOfItsKey _, NumericTerm.OccurrencesOfAKey _,
                 NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _,
                 NumericTerm.ProductOf _ -> null;
        };
    }

    /**
     * How often a value occurs among every occurrence of its place, in the containers inside the
     * elements of another.
     *
     * <p>One number and nothing beside it: how many the containers hold in all, or how many each
     * holds, is another question about how the occurrences are shared out, which a group asking it
     * beside this is one nothing here writes.
     */
    private static JointRealization amongEveryOccurrence(
            Collection<RealizationTarget> group, List<RealizationTarget.OfANumber> numbers) {
        RealizationTarget.OfANumber alike = numbers.getFirst();
        for (RealizationTarget.OfANumber each : numbers) {
            if (!each.term().equals(alike.term())) {
                return nothingSolvesAGroup();
            }
        }
        return wholly(group, List.of(alike),
                () -> new JointBuilder.ValuesAlikeAcrossContainers(alike));
    }

    /**
     * How often the value of an input occurs among every occurrence of a place, in the containers
     * inside the elements of another.
     *
     * <p>Several keys, each counted over the same place: the keys are values the row fixed, and
     * each is written as often as asked over the same containers. Nothing beside them — how many
     * the containers hold in all is another question about how the occurrences are shared out.
     */
    private static JointRealization amongEveryOccurrenceEqualToAKey(
            Collection<RealizationTarget> group, List<RealizationTarget.OfANumber> numbers) {
        TermPath place = null;
        for (RealizationTarget.OfANumber each : numbers) {
            if (!(each.term() instanceof NumericTerm.OccurrencesOfAKey asked)
                    || (place != null && !place.equals(asked.subjectPath()))) {
                return nothingSolvesAGroup();
            }
            place = asked.subjectPath();
        }
        return wholly(group, numbers,
                () -> new JointBuilder.ValuesEqualToAKeyAcrossContainers(numbers));
    }

    /**
     * What the elements of several keys an input holds come to, of the elements of one fold.
     *
     * <p>One fold, as {@link JointBuilder.UnderSeveralKeys} writes the elements of each key apart
     * from the others and puts them in one container: the keys are told apart by the same way
     * from an element to its key, and the numbers are gathered of the same elements. Numbers of
     * another way to the key, or of other elements, share elements this does not choose between.
     */
    private static JointRealization underSeveralKeys(Collection<RealizationTarget> group,
                                                     List<RealizationTarget.ACount> counts,
                                                     List<RealizationTarget.OfANumber> totals,
                                                     List<RealizationTarget.OfANumber> numbers) {
        NumericTerm.GatheredUnderItsKey first =
                ((NumericTerm.GatheredUnderAKey) totals.getFirst().term()).gathered();
        for (RealizationTarget.OfANumber each : totals) {
            NumericTerm.GatheredUnderItsKey gathered =
                    ((NumericTerm.GatheredUnderAKey) each.term()).gathered();
            if (!gathered.elements().equals(first.elements())
                    || !gathered.key().equals(first.key())) {
                return nothingSolvesAGroup();
            }
        }
        List<RealizationTarget> owned = new ArrayList<>(numbers);
        owned.addAll(counts);
        return wholly(group, owned, () -> new JointBuilder.UnderSeveralKeys(counts, totals));
    }

    /**
     * Whether {@code number} is the value of the key field of the elements the totals are
     * gathered of: what a statement counting the elements of a key reads of each, which the
     * elements are written holding and the row is read back for.
     */
    private static boolean standsAtTheKeyOfTheTotals(RealizationTarget.OfANumber number,
                                                     List<RealizationTarget.OfANumber> totals) {
        NumericTerm.GatheredUnderAKey asked =
                (NumericTerm.GatheredUnderAKey) totals.getFirst().term();
        return number.term() instanceof NumericTerm.ValueOf value
                && value.position().equals(asked.key().from(asked.gathered().elements()));
    }

    /**
     * Whether {@code count} is how many elements have the key a total in {@code numbers} is
     * gathered for: the elements of its container whose key is the value an input holds, which
     * is the statement the elements of that key meet by being its elements.
     */
    private static boolean countsTheElementsOfAKeyOf(
            RealizationTarget.ACount count, List<RealizationTarget.OfANumber> numbers) {
        return keyAskedOfTheCount(count, (NumericTerm.GatheredUnderAKey)
                numbers.getFirst().term()) != null;
    }

    /**
     * The input whose value the elements {@code count} counts have for their key — or null where
     * it counts something else: the elements of the container {@code gathered} gathers whose key
     * is the value of one input standing outside every container.
     */
    private static TermPath keyAskedOfTheCount(RealizationTarget.ACount count,
                                               NumericTerm.GatheredUnderAKey gathered) {
        RealizationTarget.AskedKey key = count.askedKey();
        TermPath elements = gathered.gathered().elements();
        return key != null && key.elements().equals(elements)
                && key.keyAt().equals(gathered.key().from(elements)) ? key.asked() : null;
    }

    /**
     * How many elements of one container meet each of some statements, with how many it holds
     * where the group asks that too.
     *
     * <p>One container. A count is of the elements of the container it names, and counts of two
     * containers written at one location are a value composed out of two collections at once,
     * which nothing here writes. Beside them, a value asked at the element itself is some element
     * standing there, which is one more thing the elements are chosen for; anything else asked
     * inside an element is not, and the group is one nothing here writes. A statement the
     * elements meet together is about the same container or the group is one nothing writes.
     */
    private static JointRealization countsOf(Collection<RealizationTarget> group,
                                             List<RealizationTarget.ACount> counts,
                                             List<RealizationTarget.ElementsMeetingTogether>
                                                     together,
                                             List<RealizationTarget.OfANumber> numbers) {
        TermPath container = counts.isEmpty() ? together.getFirst().container()
                : counts.getFirst().count().container();
        for (RealizationTarget.ACount each : counts) {
            if (!each.count().container().equals(container)) {
                return nothingSolvesAGroup();
            }
        }
        for (RealizationTarget.ElementsMeetingTogether each : together) {
            if (!each.container().equals(container)) {
                return nothingSolvesAGroup();
            }
        }
        List<RealizationTarget.OfANumber> holding = new ArrayList<>();
        List<RealizationTarget.OfANumber> elements = new ArrayList<>();
        for (RealizationTarget.OfANumber each : numbers) {
            switch (each.term()) {
                case NumericTerm.TakenOf taken
                        when taken.takenAs() instanceof TakenAs.HowManyItHolds
                        && taken.position().equals(container) -> holding.add(each);
                // The element itself, or a number inside it: some element standing there.
                case NumericTerm.ValueOf value
                        when value.position().isAtOrUnder(container.element()) ->
                        elements.add(each);
                default -> {
                    return nothingSolvesAGroup();
                }
            }
        }
        // How many it holds is one number of one container, so a second is a second target.
        if (holding.size() > 1) {
            return nothingSolvesAGroup();
        }
        RealizationTarget.OfANumber many = holding.isEmpty() ? null : holding.getFirst();
        List<RealizationTarget> answered = new ArrayList<>(counts);
        answered.addAll(together);
        answered.addAll(numbers);
        return wholly(group, answered,
                () -> new JointBuilder.SoManyMeetingEach(counts, together, many, elements));
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
                                           Collection<? extends RealizationTarget> owned,
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

        /**
         * The values to write at the group's location, answering every number it asks.
         *
         * @param keptApart what the rules of the value holding the location keep the elements of a
         *                  container written there apart at ({@link ElementsKeptApart#heldUnder}),
         *                  which a way writing a container element by element keeps beside what
         *                  the container's own names keep
         * @param inside what the value is asked to hold at positions inside it, which only a way
         *               that composes a value element by element can take
         *               ({@link #composesWhatIsInside})
         */
        Realization from(Type sourceType, List<List<String>> keptApart,
                         SequencedMap<RealizationTarget, AskedAt> demands,
                         Quantities measuring, SearchRegion within, RuleReadingContext reading,
                         DemandsInside inside);

        /**
         * One number, whose value is what every other reader of this file asks for.
         *
         * <p>Here so that a group of one is not a second way of doing what
         * {@link TermRealizations#satisfying(Type, TermOrders, NumericSet, SearchRegion,
         * RuleReadingContext)} does — it is that way, reached by the one road a caller takes to any
         * group.
         */
        record OneNumberOnItsOwn(RealizationTarget.OfANumber number) implements JointBuilder {

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                return satisfying(sourceType, keptApart, measuring.ordersOf(number.term()),
                        demands.get(number), within, reading, inside);
            }
        }

        /**
         * A tree whose search finds a line of the length asked, to the node holding the value the
         * row stands at for the search.
         *
         * <p>Apart from {@link OneNumberOnItsOwn} because the tree is written against another
         * parameter's value: the nodes above the one the search stops at are written holding
         * another value than it, and the node it stops at holds it.
         */
        record ALineToTheValue(RealizationTarget.OfANumber number) implements JointBuilder {

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                return aLineToTheValue((NumericTerm.TakenOver) number.term(), sourceType,
                        demands.get(number), measuring, within, reading);
            }
        }

        /**
         * One string holding the numbers asked of its code points — how many of each class, what
         * they come to — and that many in all where the length is asked too.
         *
         * <p><b>One string and not one for each number.</b> The numbers of one string are tied: two
         * classes that share code points count those in both, none counts more than the string is
         * long, and what the code points come to turns on which they are. A string written for
         * each number alone and put side by side would answer none of them, so the numbers are
         * chosen together and the string is written out of them.
         */
        record StringsHoldingTheirNumbers(List<RealizationTarget.OfANumber> ofItsCodePoints,
                                          RealizationTarget.OfANumber length)
                implements JointBuilder {

            public StringsHoldingTheirNumbers {
                if (ofItsCodePoints.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a string holding numbers of its code points says which numbers");
                }
                ofItsCodePoints = List.copyOf(ofItsCodePoints);
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                Map<RealizationTarget.OfANumber, Carrier> answeredOn = new LinkedHashMap<>();
                for (RealizationTarget.OfANumber each : ofItsCodePoints) {
                    answeredOn.put(each, measuring.ordersOf(each.term()).answered());
                }
                if (length != null) {
                    answeredOn.put(length, measuring.ordersOf(length.term()).answered());
                }
                return stringsHoldingTheirNumbers(answeredOn, sourceType, demands, within, reading);
            }
        }

        /** The parts of a time, each standing at what its own set admits. */
        record AtThoseTimeParts(SequencedMap<RealizationTarget.OfANumber, TakenAs.TimePart> parts)
                implements JointBuilder {

            public AtThoseTimeParts {
                if (parts.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a way of writing a value for some parts says which parts");
                }
                parts = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(parts));
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                Map<TakenAs.TimePart, NumericSet> asked = new LinkedHashMap<>();
                for (Map.Entry<RealizationTarget.OfANumber, TakenAs.TimePart> each
                        : parts.entrySet()) {
                    asked.put(each.getValue(), demands.get(each.getKey()).walking());
                }
                return atThoseParts(asked, sourceType, rootOf(parts.keySet(), measuring),
                        reading.source());
            }
        }

        /**
         * The parts of one date, each taken after the date was moved as its own number says, and
         * a date that is not moved being one moved by nothing.
         *
         * <p>The year of {@code b} and the year of {@code b} a day on are two numbers of one date,
         * and a value spelled in parts has one year to write. So a date answering them is looked
         * for among the days, where every number asked is a condition on the date itself
         * ({@link #onMovedDates}). That holds of the parts of a date nobody moved as well, so they
         * are looked for the same way and there is one search for a date and not two.
         */
        record OnThoseDateParts(
                SequencedMap<RealizationTarget.OfANumber, TakenAs.DatePart> parts,
                SequencedMap<RealizationTarget.OfANumber, DateTranslation> moved)
                implements JointBuilder {

            public OnThoseDateParts {
                if (parts.isEmpty() || !parts.keySet().equals(moved.keySet())) {
                    throw new IllegalArgumentException("a way of writing a moved date says how"
                            + " each part was moved");
                }
                parts = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(parts));
                moved = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(moved));
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                List<DatePartAsk> asks = new ArrayList<>();
                for (Map.Entry<RealizationTarget.OfANumber, TakenAs.DatePart> each
                        : parts.entrySet()) {
                    asks.add(new DatePartAsk(each.getValue(), moved.get(each.getKey()),
                            demands.get(each.getKey()).walking()));
                }
                return onMovedDates(asks, sourceType, rootOf(parts.keySet(), measuring), reading);
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
        record SolvingForTheirQuotients(SequencedMap<RealizationTarget.OfANumber, BigDecimal> by)
                implements JointBuilder {

            public SolvingForTheirQuotients {
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a solving for some quotients says which divisors they are by");
                }
                by = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(by));
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                Carrier observed = rootOf(by.keySet(), measuring);
                if (observed == null) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                NumericDomain.Bounds lies = NumericDomain.Bounds.OPEN;
                for (Map.Entry<RealizationTarget.OfANumber, BigDecimal> each : by.entrySet()) {
                    // The quotients as ends that hold nothing else. The walk below counts the
                    // numbers it admits, and a hole in the quotients is as many numbers of the
                    // place as the divisor is wide — so a set with one is a population nothing here
                    // solves a value out of, and not a set with nothing in it.
                    NumericDomain.Bounds quotients =
                            demands.get(each.getKey()).walking().asOneRun();
                    if (quotients == null) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(Set.of(
                                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)),
                                null);
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
         * One number of the place whose remainders by those divisors are the numbers asked for,
         * solved for ({@link RemainderSolutions}).
         *
         * <p><b>Solved and not walked.</b> What several remainders of one number ask is a class of
         * whole numbers, or nothing where they disagree, and the number is the class's member nearest
         * the end of the run the rules leave the place. How far apart the members are is the product
         * of the divisors, which is why no walk through them is a way to find one.
         *
         * <p>What is read of each demand is the remainders it admits, as many as a figure allows, so
         * a solving that did not try every one of them says it stopped and is never read as the rules
         * leaving no number.
         */
        record SolvingForTheirRemainders(SequencedMap<RealizationTarget.OfANumber, BigDecimal> by)
                implements JointBuilder {

            public SolvingForTheirRemainders {
                if (by.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a solving for some remainders says which divisors they are by");
                }
                by = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(by));
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                Carrier observed = rootOf(by.keySet(), measuring);
                if (observed == null) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                // Every remainder is of one place, so the run the rules leave its value is the one
                // run every demand is solved in.
                NumericDomain.Bounds run = NumericDomain.Bounds.OPEN;
                switch (valueOfThePlace(by.firstEntry().getKey().term(), within)) {
                    case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) ->
                            run = held;
                    case NumericDomain.FormProjection.NothingIsLeft _ -> {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    case null -> { }
                }
                List<RemainderSolutions.Demand> asked = new ArrayList<>();
                for (Map.Entry<RealizationTarget.OfANumber, BigDecimal> each : by.entrySet()) {
                    AskedAt of = demands.get(each.getKey());
                    if (of == null) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    asked.add(new RemainderSolutions.Demand(each.getValue(), of.walking(),
                            of.named()));
                }
                RuleReadingSource ruleSource = reading.source();
                return firstThatBuilds(walkIsOfTheWholeQuestion(demands.values()),
                        offeredBy(RemainderSolutions.solve(asked,
                                valueOfThePlaceHeldTo(by.firstEntry().getKey().term(), run, within),
                                observed)),
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
        record ItsOwnValueAndWhatIsTakenOfIt(RealizationTarget.OfANumber itself,
                                            List<RealizationTarget.OfANumber> takenOfIt)
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
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
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
                for (RealizationTarget.OfANumber each : takenOfIt) {
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
                        admitting(onTheOrder(stands, orders, standsAt.named(), within,
                                        UsualPlaces.of(orders.term(), orders.answered(),
                                                reading.today())),
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
        record TotalsOfOneContainer(List<RealizationTarget.OfANumber> whatItComesTo,
                                    RealizationTarget.OfANumber manyItHolds)
                implements JointBuilder {

            public TotalsOfOneContainer {
                if (whatItComesTo.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a container composed for its totals is asked for at least one");
                }
                whatItComesTo = List.copyOf(whatItComesTo);
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                ContainersAddingUp.HowManyIsAskedFor holding = null;
                if (manyItHolds != null) {
                    TermOrders counted = measuring.ordersOf(manyItHolds.term());
                    AskedAt holdsAt = demands.get(manyItHolds);
                    NumericSet many = holdsAt == null ? null : holdsAt.walking();
                    if (counted == null || counted.answered() == null || many == null) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    // Where the rules leave the size on the way, which the container's own walk
                    // asks of the region already. What is handed over here is the group's demand
                    // and not the way, so neither reading stands in for the other.
                    if (within != null && within.projectionOf(manyItHolds.term())
                            instanceof NumericDomain.FormProjection.NothingIsLeft) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    holding = new ContainersAddingUp.HowManyIsAskedFor(many, counted.answered());
                }
                List<TermOrders> adding = new ArrayList<>();
                List<Tried> candidates = new ArrayList<>();
                for (RealizationTarget.OfANumber each : whatItComesTo) {
                    TermOrders adds = measuring.ordersOf(each.term());
                    AskedAt comesToAt = demands.get(each);
                    NumericSet total = comesToAt == null ? null : comesToAt.walking();
                    if (adds == null || total == null) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    adding.add(adds);
                    candidates.add(onTheOrder(total, adds, comesToAt.named(), within,
                            UsualPlaces.of(adds.term(), adds.answered(), reading.today())));
                }
                ContainersAddingUp.HowManyIsAskedFor sizes = holding;
                Together together = Together.of(candidates);
                return firstThatBuilds(walkIsOfTheWholeQuestion(demands.values()),
                        together.each(), together.rest(),
                        at -> ContainersAddingUp.to(at.getFirst(), sourceType, keptApart,
                                adding.getFirst(), within, reading, sizes,
                                alsoAddingUp(adding, at), inside));
            }

            /** The totals after the first, each with the number tried for it. */
            private static List<ContainersAddingUp.AlsoAddingUp> alsoAddingUp(
                    List<TermOrders> adding, List<Place> at) {
                List<ContainersAddingUp.AlsoAddingUp> also = new ArrayList<>();
                for (int each = 1; each < adding.size(); each++) {
                    also.add(new ContainersAddingUp.AlsoAddingUp(adding.get(each), at.get(each)));
                }
                return also;
            }
        }

        /**
         * A container with so many of its elements meeting each statement, and holding as many
         * elements as {@code manyItHolds} asks where it asks.
         *
         * <p>Composed out of the counts and read for none of them. Which elements a container holds
         * is what every count of it turns on together, so they are one question and the container
         * is written once ({@link CardinalityComposer}).
         *
         * @param together    statements the elements are to meet together, each one of several ways
         * @param manyItHolds how many elements the container holds, or null where nothing asks
         * @param standingAt  the element itself, each asked to stand in a set — which some element
         *                    of the container does
         */
        record SoManyMeetingEach(List<RealizationTarget.ACount> counts,
                                 List<RealizationTarget.ElementsMeetingTogether> together,
                                 RealizationTarget.OfANumber manyItHolds,
                                 List<RealizationTarget.OfANumber> standingAt)
                implements JointBuilder {

            public SoManyMeetingEach {
                if (counts.isEmpty() && together.isEmpty()) {
                    throw new IllegalArgumentException("a container composed for its counts is"
                            + " asked for at least one, or for a statement its elements meet");
                }
                counts = List.copyOf(counts);
                together = List.copyOf(together);
                standingAt = List.copyOf(standingAt);
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                return CardinalityComposer.compose(sourceType, keptApart, counts, together,
                        demands, manyItHolds, standingAt, measuring, within, reading);
            }
        }

        /**
         * A container holding some element as often as asked, and as many elements as
         * {@code manyItHolds} asks where it asks.
         *
         * <p>Composed out of how often and read for nothing: which values the elements hold and how
         * many hold each is what the number turns on, so the container is written once
         * ({@link CardinalityComposer#composeAlike}).
         *
         * @param alike       how often some element's value occurs
         * @param manyItHolds how many elements the container holds, or null where nothing asks
         */
        record ElementsAlikeAsOftenAsAsked(RealizationTarget.OfANumber alike,
                                           RealizationTarget.OfANumber manyItHolds)
                implements JointBuilder {

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                return CardinalityComposer.composeAlike(sourceType, keptApart, alike, manyItHolds,
                        demands, measuring, within, reading);
            }
        }

        /**
         * Containers inside the elements of another holding some value as often as asked, in all
         * of them put end to end ({@link CardinalityComposer#composeAcrossContainers}).
         *
         * @param alike how often some value occurs among every occurrence of its place
         */
        record ValuesAlikeAcrossContainers(RealizationTarget.OfANumber alike)
                implements JointBuilder {

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                return CardinalityComposer.composeAcrossContainers(sourceType, keptApart, alike,
                        demands, measuring, within, reading);
            }
        }

        /**
         * Containers inside the elements of another holding the value of an input as often as
         * asked, in all of them put end to end
         * ({@link CardinalityComposer#composeAcrossContainersEqualToAKey}).
         *
         * @param asked how often each key's value occurs among every occurrence of their place
         */
        record ValuesEqualToAKeyAcrossContainers(List<RealizationTarget.OfANumber> asked)
                implements JointBuilder {

            public ValuesEqualToAKeyAcrossContainers {
                asked = List.copyOf(asked);
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                nothingInside(inside);
                return CardinalityComposer.composeAcrossContainersEqualToAKey(sourceType,
                        keptApart, asked, demands, measuring, within, reading);
            }
        }

        /**
         * A container holding the elements of each of several keys an input holds, the elements
         * of a key coming to the number asked of it and being as many as the count asked of them.
         *
         * <p>Composed one key at a time and put together. The elements of a key are written
         * holding it ({@link TermRealizations#underAKey}), so the elements of another are none of
         * its own, and the container is the elements of each in turn. Keys the row holds at one
         * value are one key, whose elements come to the one number asked of them all; two numbers
         * asked of it are elements chosen for both, which nothing here does.
         *
         * <p>A key asked only how many elements have it is written as a key whose number is the
         * one a total of the group asks, since nothing else says what its elements come to; one
         * asked to have none is written with none.
         *
         * <p>Offered row by row, the ways one key is composed taken beside the ways of the others
         * in turn, and not every combination of them: what is left is said as a way a total is
         * spread that was not tried.
         *
         * @param counts how many elements have each key, where that is asked beside the numbers
         */
        record UnderSeveralKeys(List<RealizationTarget.ACount> counts,
                                List<RealizationTarget.OfANumber> numbers)
                implements JointBuilder {

            public UnderSeveralKeys {
                counts = List.copyOf(counts);
                numbers = List.copyOf(numbers);
            }

            @Override
            public Realization from(Type sourceType, List<List<String>> keptApart,
                                    SequencedMap<RealizationTarget, AskedAt> demands,
                                    Quantities measuring, SearchRegion within,
                                    RuleReadingContext reading, DemandsInside inside) {
                List<Place> keys = new ArrayList<>();
                List<RealizationTarget.OfANumber> ofEachKey = new ArrayList<>();
                List<AskedAt> askedOfEachKey = new ArrayList<>();
                List<NumericSet> howManyOfEachKey = new ArrayList<>();
                // The keys only counted: no number is asked of their elements.
                List<Boolean> onlyCounted = new ArrayList<>();
                List<List<RealizationTarget.ACount>> countsOfEachKey = new ArrayList<>();
                for (RealizationTarget.OfANumber number : numbers) {
                    NumericTerm.GatheredUnderAKey term =
                            (NumericTerm.GatheredUnderAKey) number.term();
                    Place key = within == null ? null : CardinalityComposer.settled(within,
                            new NumericTerm.ValueOf(term.asked()));
                    if (key == null) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(
                                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)),
                                "`" + term.asked() + "` stands at no one value, so what is"
                                        + " gathered for it is not known");
                    }
                    int at = 0;
                    while (at < keys.size() && !keys.get(at).sameAs(key)) {
                        at++;
                    }
                    if (at == keys.size()) {
                        keys.add(key);
                        ofEachKey.add(number);
                        askedOfEachKey.add(demands.get(number));
                        howManyOfEachKey.add(null);
                        onlyCounted.add(false);
                        countsOfEachKey.add(new ArrayList<>());
                        continue;
                    }
                    // Two parameters holding one value are one key, whose elements come to what
                    // both ask: one number where the two asked are, or the point of the one that
                    // the other holds.
                    NumericTerm.GatheredUnderItsKey held =
                            ((NumericTerm.GatheredUnderAKey) ofEachKey.get(at).term()).gathered();
                    TermOrders orders = measuring.ordersOf(number.term());
                    AskedAt agreed = !held.equals(term.gathered()) ? null
                            : agreed(askedOfEachKey.get(at), demands.get(number),
                                    orders == null ? null : orders.answered());
                    if (agreed == null) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(Set.of(
                                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)),
                                "two numbers are asked of the elements of one key");
                    }
                    askedOfEachKey.set(at, agreed);
                }
                // How many elements a key has, asked of the key whose elements the count is of; two
                // counts of one key's elements are one question, asked alike or not at all.
                NumericTerm.GatheredUnderAKey gathered =
                        (NumericTerm.GatheredUnderAKey) numbers.getFirst().term();
                for (RealizationTarget.ACount count : counts) {
                    TermPath askedOfTheKey = keyAskedOfTheCount(count, gathered);
                    Place key = within == null ? null : CardinalityComposer.settled(within,
                            new NumericTerm.ValueOf(askedOfTheKey));
                    if (key == null) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(
                                Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)),
                                "`" + askedOfTheKey + "` stands at no one value, so how many"
                                        + " elements have it is not known");
                    }
                    int at = 0;
                    while (at < keys.size() && !keys.get(at).sameAs(key)) {
                        at++;
                    }
                    if (at == keys.size()) {
                        // Nothing says what its elements come to, so they are written to come to
                        // what the first total of the group asks of its own: one of the numbers
                        // they may come to, and the way this composes them at all.
                        keys.add(key);
                        ofEachKey.add(numbers.getFirst());
                        askedOfEachKey.add(demands.get(numbers.getFirst()));
                        howManyOfEachKey.add(null);
                        onlyCounted.add(true);
                        countsOfEachKey.add(new ArrayList<>());
                    }
                    countsOfEachKey.get(at).add(count);
                    AskedAt asked = demands.get(count);
                    NumericSet wanted = asked == null ? null : asked.walking();
                    NumericSet had = howManyOfEachKey.get(at);
                    if (!onlyCounted.get(at) && had != null && !had.equals(wanted)) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(Set.of(
                                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)),
                                "two counts are asked of the elements of one key");
                    }
                    howManyOfEachKey.set(at, wanted);
                }
                List<List<FixtureTemplate>> ways = new ArrayList<>();
                CompositionShortfall rest = CompositionShortfall.NONE;
                for (int each = 0; each < keys.size(); each++) {
                    NumericSet howMany = howManyOfEachKey.get(each);
                    // A key asked to have no element is written with none.
                    if (onlyCounted.get(each) && countsOfEachKey.get(each).stream()
                            .allMatch(count -> {
                                AskedAt wanted = demands.get(count);
                                return wanted != null
                                        && wanted.walking().holds(Count.of(0), Carrier.WHOLE)
                                        && !wanted.walking().holds(Count.of(1), Carrier.WHOLE);
                            })) {
                        continue;
                    }
                    Realization one = underAKey(sourceType, keptApart,
                            measuring.ordersOf(ofEachKey.get(each).term()),
                            askedOfEachKey.get(each), within, reading, inside, howMany,
                            keys.get(each));
                    if (!(one instanceof Realization.Built built)) {
                        return asked(one, keys, onlyCounted);
                    }
                    ways.add(built.values());
                    rest = rest.and(built.rest());
                }
                int rows = ways.stream().mapToInt(List::size).max().orElse(0);
                List<FixtureTemplate> together = new ArrayList<>();
                for (int row = 0; row < rows; row++) {
                    List<FixtureTemplate> parts = new ArrayList<>();
                    for (List<FixtureTemplate> each : ways) {
                        parts.add(each.get(row % each.size()));
                    }
                    FixtureTemplate joined = FixtureTemplate.concatenated(parts);
                    if (joined == null) {
                        return new Realization.Unexhausted(CompositionShortfall.writing(Set.of(
                                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)),
                                "a container that is not a list written bare is not put together"
                                        + " out of the elements of several keys");
                    }
                    together.add(joined);
                }
                return asked(new Realization.Built(together, rest.and(
                        CompositionShortfall.writing(
                                Set.of(CompositionRepertoire.WAYS_A_TOTAL_IS_SPREAD)))),
                        keys, onlyCounted);
            }

            /**
             * What came of the keys, said to be some of the ways they may be asked together
             * where there is more than one key or one is only counted: the values they were
             * placed at and the number a key only counted came to are a way to try, and a row not
             * written is not a row there is none of.
             */
            private static Realization asked(Realization made, List<Place> keys,
                                              List<Boolean> onlyCounted) {
                return keys.size() > 1 || onlyCounted.contains(true)
                        ? someOf(made, CompositionRepertoire.KEYS_OF_ONE_FOLD_ASKED_TOGETHER)
                        : made;
            }

            /**
             * What two parameters holding one key ask of its elements, as one asking: the one asked
             * where they ask alike, or the point of the one that the other's set holds — and null
             * where they ask what no one set of elements is chosen for.
             */
            private static AskedAt agreed(AskedAt one, AskedAt other, Carrier on) {
                if (one == null || other == null) {
                    return one == null ? other : one;
                }
                NumericSet asked = one.walking();
                NumericSet alsoAsked = other.walking();
                if (asked.equals(alsoAsked)) {
                    return one;
                }
                if (on == null) {
                    return null;
                }
                if (asked instanceof NumericSet.At point && alsoAsked.holds(point.value(), on)) {
                    return one;
                }
                return alsoAsked instanceof NumericSet.At point && asked.holds(point.value(), on)
                        ? other : null;
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
        private static Carrier rootOf(Collection<RealizationTarget.OfANumber> group,
                                      Quantities measuring) {
            Carrier observed = null;
            for (RealizationTarget.OfANumber target : group) {
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
        return allSatisfying(sourceType, List.of(), demands, measuring, within, reading,
                DemandsInside.NOTHING);
    }

    /**
     * The same, with the value asked to hold {@code inside} at positions inside it as well, and
     * held by a value whose rules keep the elements of a container written there apart at
     * {@code keptApart} ({@link JointBuilder#from}).
     *
     * <p>Only for a group whose value is composed rather than read ({@link #composesWhatIsInside}).
     * A value written as one number — a literal, a moment spelled in parts — has no positions
     * inside it to hold anything, and a caller handing demands to one has asked for a value nothing
     * here writes.
     */
    static Realization allSatisfying(Type sourceType, List<List<String>> keptApart,
                                     SequencedMap<RealizationTarget, AskedAt> demands,
                                     Quantities measuring,
                                     SearchRegion within,
                                     RuleReadingContext reading,
                                     DemandsInside inside) {
        // What type the value is written at is the caller's answer and is settled before this is
        // asked. Read here as one more thing that could be missing, a location whose write path
        // this reading has no type for would come back as a group nothing solves — which is a
        // sentence about what this compiler cannot compose, said of a question nobody asked.
        assert sourceType != null : "a group is realized at the type its caller settled";
        // Numbers of one location, some of them taken of its value: chosen among the values its
        // rules name, where they name finitely many. Nothing inside such a value is composed, so a
        // group asking for that is left to the way that composes it.
        if (inside.isEmpty()) {
            SequencedMap<TermOrders, AskedAt> numbers = numbersOf(demands, measuring);
            if (numbers != null) {
                Realization named = amongTheValuesNamed(sourceType, numbers, within, reading);
                if (named != null) {
                    return named;
                }
            }
        }
        return switch (jointRealizationOf(demands.keySet())) {
            // Which population, and no detail beside it: nothing was walked here, so there is
            // nothing this found to tell a reader.
            case JointRealization.Missing(CompositionRepertoire notAllOf) ->
                    new Realization.Unexhausted(CompositionShortfall.writing(Set.of(notAllOf)), null);
            case JointRealization.Supported(JointBuilder builder) ->
                    builder.from(sourceType, keptApart, demands, measuring, within, reading,
                            inside);
        };
    }

    /**
     * Each number of {@code demands} by the orders it is read on and the set asked of it, where
     * every demand is a number read of one place and one of them is taken of its value — or null
     * where that is not so.
     *
     * <p>A group of nothing but the value itself is chosen out of the region already, as one
     * number of it is ({@link #standing}).
     */
    private static SequencedMap<TermOrders, AskedAt> numbersOf(
            SequencedMap<RealizationTarget, AskedAt> demands, Quantities measuring) {
        SequencedMap<TermOrders, AskedAt> out = new LinkedHashMap<>();
        boolean takenOfIt = false;
        for (Map.Entry<RealizationTarget, AskedAt> each : demands.entrySet()) {
            if (!(each.getKey() instanceof RealizationTarget.OfANumber number)
                    || number.term().atOnePosition() == null) {
                return null;
            }
            takenOfIt |= !(number.term() instanceof NumericTerm.ValueOf);
            out.put(measuring.ordersOf(number.term()), each.getValue());
        }
        return takenOfIt ? out : null;
    }

    /**
     * Whether the value answering {@code group} is composed element by element, so that what its
     * elements hold at positions inside them can be asked of it beside the numbers.
     *
     * <p>A container filled to a total is: each element is planned and built, and a position the
     * caller fixed is one more thing the plan is made against. Every other way of writing a value
     * for a group writes it as one number or reads it off a value it was handed, and nothing inside
     * such a value is chosen for anything to be asked of.
     */
    static boolean composesWhatIsInside(Collection<RealizationTarget> group) {
        if (!(jointRealizationOf(group) instanceof JointRealization.Supported(JointBuilder builder))) {
            return false;
        }
        return switch (builder) {
            case JointBuilder.TotalsOfOneContainer _ -> true;
            case JointBuilder.OneNumberOnItsOwn only -> switch (only.number().term()) {
                case NumericTerm.TakenOver over ->
                        over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
                case NumericTerm.TakenOf taken ->
                        taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
                // A string is chosen whole, and what its code points come to is read off it: no
                // element of it is composed.
                case NumericTerm.ValueOf _, NumericTerm.CodePointClassCount _,
                     NumericTerm.CodePointValueSum _, NumericTerm.CodePointAt _,
                     NumericTerm.WholeUnitsOf _, NumericTerm.Multiplicity _,
                     NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                     NumericTerm.ExtremeOfItsKey _, NumericTerm.GatheredUnderItsKey _,
                     NumericTerm.GatheredUnderAKey _, NumericTerm.ProductOf _ -> false;
            };
            // Each element is chosen for what it answers of the statements, out of values of the
            // element's own number; nothing else inside it is planned.
            case JointBuilder.SoManyMeetingEach _, JointBuilder.ElementsAlikeAsOftenAsAsked _,
                 JointBuilder.ValuesAlikeAcrossContainers _,
                 JointBuilder.ValuesEqualToAKeyAcrossContainers _,
                 JointBuilder.UnderSeveralKeys _ -> false;
            case JointBuilder.StringsHoldingTheirNumbers _,
                 JointBuilder.AtThoseTimeParts _, JointBuilder.OnThoseDateParts _,
                 JointBuilder.SolvingForTheirQuotients _,
                 JointBuilder.SolvingForTheirRemainders _,
                 JointBuilder.ItsOwnValueAndWhatIsTakenOfIt _,
                 JointBuilder.ALineToTheValue _ -> false;
        };
    }

    /**
     * Refuses demands inside a value a way of writing one has no positions inside of to hold.
     *
     * <p>Asked of {@link #composesWhatIsInside} before anything here is reached, so a caller that
     * gets this far with demands has handed them to the wrong builder — which is this compiler's
     * mistake, and said loudly rather than by a value composed as though they were not there.
     */
    private static void nothingInside(DemandsInside inside) {
        if (!inside.isEmpty()) {
            throw new IllegalArgumentException("a value written as one number holds nothing inside"
                    + " it to be asked for: " + inside);
        }
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
        // A value of the position itself is chosen out of the region already ({@link #standing}).
        if (!(orders.term() instanceof NumericTerm.ValueOf)) {
            SequencedMap<TermOrders, AskedAt> one = new LinkedHashMap<>();
            one.put(orders, asked);
            Realization named = amongTheValuesNamed(sourceType, one, within, reading);
            if (named != null) {
                return named;
            }
        }
        return satisfying(sourceType, List.of(), orders, asked, within, reading,
                DemandsInside.NOTHING);
    }

    /**
     * The values the location's rules name that answer every number asked of it, or null where
     * there are none to choose among.
     *
     * <p>Where the reading admits finitely many values at the location, those are every value a
     * row can write there, whichever rules narrowed them — the location's own type, a record
     * holding it, the element of a container. So a number taken of the location is written by
     * choosing among them, each read through its term as a row holding it would be
     * ({@link TermOrders#readOf}); a value written for the number alone is one those rules refuse.
     * The set is the one a border on the number is refused by ({@code HeldValues}), so a number a
     * border owes a row at is one some value of it comes to.
     *
     * <p>Every value of the set is tried, each read through every number at once
     * ({@link ReadingsOfEachValue}), and the set holds every value the location can hold.
     * So where every number is walked as the whole of what it is asked about, none answering is an
     * answer about the model and is said as one; where a caller picked a number to try, it is an
     * answer about that number, which is no answer about the ones beside it.
     *
     * <p>Null where the numbers are not all of one location, where the location admits no finite
     * set, or where a value of it is read as no number of a term asked: the accounts write values
     * there as they would anywhere.
     *
     * @param asked each number asked of the location, by the orders it is read on
     */
    private static Realization amongTheValuesNamed(Type sourceType,
                                                   SequencedMap<TermOrders, AskedAt> asked,
                                                   SearchRegion within,
                                                   RuleReadingContext reading) {
        if (sourceType == null || within == null || asked.isEmpty()) {
            return null;
        }
        TermOrders first = asked.firstEntry().getKey();
        Carrier observed = first.observed();
        if (observed == null || first.term().atOnePosition() == null) {
            return null;
        }
        // Read through the orders this was handed, which are the ones each number was asked on.
        ReadingsOfEachValue named = ReadingsOfEachValue.of(
                within.admittedAt(first.term().atOnePosition()), List.copyOf(asked.keySet()));
        if (named == null) {
            return null;
        }
        List<Place> answering = new ArrayList<>();
        for (ReadingsOfEachValue.Read each : named.each()) {
            boolean answers = true;
            for (Map.Entry<TermOrders, AskedAt> one : asked.entrySet()) {
                answers &= one.getValue().walking().holds(
                        each.numbers().get(one.getKey().term()), one.getKey().answered());
            }
            if (answers) {
                answering.add(observed.placeOf(each.value()));
            }
        }
        RuleReadingSource ruleSource = reading.source();
        WornNames wears = namesOf(sourceType, ruleSource);
        if (!(wears instanceof WornNames.Spelled worn)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    ((WornNames.Unwritable) wears).why());
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (Place each : answering) {
            FixtureTemplate bare = FixtureTemplate.on(observed, each,
                    ruleSource.symbols().scope()::reach);
            // A value this writes no literal for is one the set holds and this cannot offer, so
            // none answering would no longer be an answer about the model.
            if (bare == null) {
                return null;
            }
            out.add(RepresentativeSource.under(worn.names(), bare));
        }
        if (!out.isEmpty()) {
            return Realization.Built.whole(out);
        }
        boolean theWholeQuestion = asked.values().stream()
                .allMatch(AskedAt::walkIsOfTheWholeQuestion);
        return new Realization.None(theWholeQuestion
                ? Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE
                : Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }

    /** The same, with the value asked to hold {@code inside} at positions inside it as well, and
     *  held by a value whose rules keep its elements apart at {@code keptApart}. */
    private static Realization satisfying(Type sourceType, List<List<String>> keptApart,
                                          TermOrders orders, AskedAt asked,
                                          SearchRegion within,
                                          RuleReadingContext reading, DemandsInside inside) {
        if (sourceType == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Which number is being written for, read off the answer that says which number it is of.
        // Handed in beside it, it was a second name for the same thing and a caller could give two
        // — and this would then write a value for one number on the order of another.
        RealizationTarget.OfANumber target = RealizationTarget.of(orders.term());
        return switch (target.term()) {
            // Written by the carrier the line was drawn on, and wearing every name the position
            // declares. Read off the boundary's own shape instead, a count on one carrier could be
            // written as a literal of another — which is how a date-time's second count reached a
            // row as an `Int`, and the decoder refused it with the report saying only that every
            // value tried had been refused.
            case NumericTerm.ValueOf _ -> {
                nothingInside(inside);
                yield standing(sourceType, orders, asked, within, reading);
            }
            // Written as the value it is the end of, at the place it is taken of, on the order the
            // values stand on ({@link RealizationTarget.AtItsKey}).
            case NumericTerm.ExtremeOfItsKey end -> {
                nothingInside(inside);
                // The end of the steps the values fall in is written as the end that falls in the
                // step asked for: the first value of the step, as a step of one value is.
                yield end.through() == null
                        ? standing(sourceType, orders, asked, within, reading)
                        : multipliedBackAt(BigDecimal.valueOf(end.perUnit()),
                                UsualPlaces.of(orders.term(), orders.answered(), reading.today()),
                                sourceType, orders, asked, within, reading.source());
            }
            // Written as the container of the elements, holding elements of one key that come to
            // the number ({@link RealizationTarget.UnderItsKey}).
            case NumericTerm.GatheredUnderItsKey _ -> underItsKey(sourceType, keptApart, orders,
                    asked, within, reading, inside, null);
            case NumericTerm.GatheredUnderAKey _ -> underAKey(sourceType, keptApart, orders,
                    asked, within, reading, inside, null, null);
            // Replaced by the numbers its two forms are of before a row is composed
            // ({@code Generator}), so nothing is written for it as one value.
            case NumericTerm.ProductOf _ -> new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            case NumericTerm.TakenOf taken -> taken(taken.takenAs(), taken.arguments(),
                    taken.transformation(), sourceType, keptApart, orders, asked, within,
                    reading, inside);
            case NumericTerm.CodePointClassCount counted -> {
                nothingInside(inside);
                yield holdingThatManyOfAClass(counted.counted(), counted.through(), sourceType,
                        asked, orders, reading);
            }
            // A string written for its code points alone, which is the search that writes one for
            // several numbers of a string, asked one.
            case NumericTerm.CodePointValueSum _, NumericTerm.CodePointAt _ -> {
                nothingInside(inside);
                SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
                demands.put(target, asked);
                Map<RealizationTarget.OfANumber, Carrier> answeredOn = new LinkedHashMap<>();
                answeredOn.put(target, orders.answered());
                yield stringsHoldingTheirNumbers(answeredOn, sourceType, demands, within, reading);
            }
            case NumericTerm.TakenOver over -> overARun(over.takenAs(), sourceType, keptApart,
                    orders, asked, within, reading, inside);
            // Written as the first value of the step asked for: the step times the unit, which
            // falls in that step and reads back as it.
            case NumericTerm.WholeUnitsOf units -> {
                nothingInside(inside);
                yield multipliedBackAt(BigDecimal.valueOf(units.perUnit()),
                        UsualPlaces.of(orders.term(), orders.answered(), reading.today()),
                        sourceType, orders, asked, within, reading.source());
            }
            // Written by composing the container its elements stand in, which a value of one
            // element's type is not: a group holding it is never answered by one number alone
            // ({@link #jointRealizationOf}).
            case NumericTerm.Multiplicity among -> throw new IllegalStateException(
                    among + " is written by composing its container, and no value of one element"
                            + " is asked for it");
            case NumericTerm.OccurrencesOfItsValue among -> throw new IllegalStateException(
                    among + " is written by composing the containers its occurrences stand in,"
                            + " and no value of one element is asked for it");
            case NumericTerm.OccurrencesOfAKey ofAKey -> throw new IllegalStateException(
                    ofAKey + " is written by composing the containers its occurrences stand in,"
                            + " and no value of one element is asked for it");
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
                onTheOrder(asked.walking(), orders, asked.named(), within,
                        UsualPlaces.of(orders.term(), carrier, reading.today())),
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
    private static Realization taken(TakenAs how, TakenArguments arguments,
                                     ValueTransformation from, Type sourceType,
                                     List<List<String>> keptApart,
                                     TermOrders orders, AskedAt asked,
                                     SearchRegion within,
                                     RuleReadingContext reading, DemandsInside inside) {
        RuleReadingSource ruleSource = reading.source();
        NumericSet wanted = asked.walking();
        // Only a total is composed element by element, so only it has anything inside to hold.
        if (!(how instanceof TakenAs.TheSumOfWhatItHolds)) {
            nothingInside(inside);
        }
        return switch (how) {
            // A container has no order of its own and is built out of what it holds, so this arm
            // takes none. That is the arm's own answer and not an order standing in for nothing.
            case TakenAs.HowManyItHolds _ ->
                    holding(sourceType, keptApart, asked, orders, within, reading);
            // A container whose elements come to the total, which is what a row has to hold for
            // this number to be there. What that takes is choosing how many elements and what each
            // of them holds — one question whether the number is added up out of the container
            // itself or out of a path inside its elements, and answered for both in one place.
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(asked, sourceType, keptApart, orders,
                    within, reading, inside);
            // And this one writes on the order the value is written on. Written on the order the
            // answer is measured on, the thirteenth hour would be offered as the thirteenth second —
            // the same mistake the reading makes in the other direction, which is why the pair
            // travels this far and the arm takes the end (#1027).
            case TakenAs.PartOfTime taken -> atThoseParts(Map.of(taken.part(), wanted), sourceType,
                    orders.observed(), ruleSource);
            // And this one looks among the days, where the date as it stands is the date moved by
            // nothing.
            case TakenAs.PartOfDate taken -> onMovedDates(
                    List.of(new DatePartAsk(taken.part(), from.translation(), wanted)),
                    sourceType, orders.observed(), reading);
            // And this one multiplies back. What a quotient is taken of is a whole number and what
            // it answers is one, so both ends are the order the value is written on.
            case TakenAs.TheTruncatingQuotient taken ->
                    atThatQuotient(taken.read(arguments), sourceType, orders, asked,
                            within, ruleSource);
            // And this one writes the residue itself, which is its own remainder.
            case TakenAs.TheFloorRemainder taken ->
                    atThatRemainder(taken.read(arguments), sourceType, orders, asked,
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
    static Realization firstThatBuilds(boolean walkedTheWholeQuestion, Tried tried,
                                       Function<Place, Realization> of) {
        return firstThatBuilds(walkedTheWholeQuestion, tried.numbers(), tried.rest().shortfall(),
                of);
    }

    /**
     * The same, over whatever a value is built for: one number, or the numbers of several totals
     * together ({@link Together}).
     *
     * @param handedOver what whatever handed the numbers over left, every reason of every walk
     *                   that did: none where it handed over all there were
     */
    static <T> Realization firstThatBuilds(boolean walkedTheWholeQuestion, List<T> numbers,
                                           CompositionShortfall handedOver,
                                           Function<T, Realization> of) {
        // Everything every number that built nothing came to without, taken as one shortfall so
        // that no vocabulary of it is left behind here. The rules leaving no number at one of the
        // numbers handed over says nothing about the next: this walk is over the numbers, and that
        // one was a value's answer, whose shortfall is none.
        CompositionShortfall met = CompositionShortfall.NONE;
        Realization last = null;
        for (T number : numbers) {
            Realization made = of.apply(number);
            if (made instanceof Realization.Built built) {
                return built;
            }
            last = made;
            met = met.and(made.shortfall());
        }
        // Why there were no more to try, said by whatever handed them over. Worked out here, this
        // would be the one place that knows what every account's numbers are and how it walks them,
        // which is what handing the reason over is for.
        met = met.and(handedOver);
        if (!met.figures().isEmpty()) {
            return new Realization.Stopped(met);
        }
        if (!met.nothing()) {
            return new Realization.Unexhausted(met,
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
        if (numbers.isEmpty() && handedOver.nothing() && walkedTheWholeQuestion) {
            return new Realization.NoNumberTheDeclarationsAdmit();
        }
        return last instanceof Realization.None none ? none
                : new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
    }

    /**
     * Containers inside the elements of a container, holding as many occurrences of the run's path
     * in all as one of those numbers, from none upward as every count is offered.
     *
     * <p>Only of a run no one container holds: a count of the elements of one container is a
     * taking of that container's place, and no term over a run is made for it
     * ({@code NumericTerm.TakenOver.of}).
     */
    private static Realization counting(AskedAt asked, Type sourceType,
                                        List<List<String>> keptApart, TermOrders orders,
                                        SearchRegion within, RuleReadingContext reading,
                                        DemandsInside inside) {
        if (!(orders.term() instanceof NumericTerm.TakenOver over)) {
            throw new IllegalStateException(orders.term() + " is no count of a run");
        }
        return switch (over.source()) {
            case RunSource.FlattenedOccurrences flat -> {
                NestedContainersAddingUp nested = new NestedContainersAddingUp(flat.subjectPath());
                yield firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                        wholeNumbers(asked.walking(), orders.answered(), 0, Integer.MAX_VALUE,
                                CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(),
                                UsualPlace.NONE),
                        count -> nested.holding(count, sourceType, keptApart, orders, within,
                                reading, inside));
            }
            case RunSource.ReachableNodes nodes -> {
                nothingInside(inside);
                yield nodes.container().isEmpty()
                        ? firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                                wholeNumbers(asked.walking(), orders.answered(), 0,
                                        Integer.MAX_VALUE,
                                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(),
                                        UsualPlace.NONE),
                                count -> nodesBelowARoot(count, sourceType, keptApart, reading))
                        : treesNotWritten("nothing here writes a tree for how many values its"
                                + " nodes hold in `" + String.join(".", nodes.container())
                                + "`");
            }
            case RunSource.ProjectedOccurrences _, RunSource.ComputedOccurrences _ ->
                    throw new IllegalStateException(orders.term() + " is a count of a run one"
                            + " container holds, which is a taking of that container's place");
            // How many keys two maps share is a number nothing here asks of a row.
            case RunSource.JoinedOccurrences _ -> new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            // Written against the value the row stands at for the search, which no group of more
            // than the one number is composed with ({@link JointBuilder.ALineToTheValue}).
            case RunSource.SearchedLine _ -> {
                nothingInside(inside);
                yield linesNotWritten("a line asked beside other numbers of the same tree is not"
                        + " written");
            }
        };
    }

    /**
     * A tree of as many nodes as {@code answer}: the container below the root holding one fewer,
     * each a node holding nothing below it, the root being the one more. None at nought, which no
     * tree is. Where the rules hold what a node holds below it to fewer, a tree of that many is
     * deeper than this writes, which is said as a tree this writes none of and never as a count no
     * tree comes to.
     */
    private static Realization nodesBelowARoot(Place answer, Type sourceType,
                                               List<List<String>> keptApart,
                                               RuleReadingContext reading) {
        int many = CountDomain.asCount(answer);
        if (many == 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE);
        }
        if (many < 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Realization below = holdingExactly(sourceType, keptApart,
                Count.of(BigDecimal.valueOf(many - 1)), ElementsHeldTo.NOTHING, reading);
        return below instanceof Realization.None
                ? treesNotWritten("a tree of " + many + " nodes is deeper than a root and the"
                        + " nodes below it")
                : below;
    }

    /**
     * A tree whose search finds a line of as many nodes as one of the numbers asked: none where no
     * node holds the value searched for, and otherwise a chain of as many nodes, each the only
     * element below the one above it, of which the last holds that value and none above it does.
     *
     * <p>The value is the one the row stands at for the search, which is fixed before the tree is
     * written ({@link RealizationTarget#keyAskedFor}); the nodes above the last hold another value
     * of the same field. Each node is otherwise written from its type, with the two fields given.
     * Where a part of this is not one the type lets be written — the field is not a single field of
     * the node, the nodes below are not a list, no other value than the one searched for is there
     * to write — it is said as a tree this does not write, and never as a length no tree has.
     */
    private static Realization aLineToTheValue(NumericTerm.TakenOver over, Type sourceType,
                                               AskedAt asked, Quantities measuring,
                                               SearchRegion within, RuleReadingContext reading) {
        RunSource.SearchedLine line = (RunSource.SearchedLine) over.source();
        TermOrders orders = measuring.ordersOf(over);
        TermOrders keyOrders = measuring.ordersOf(new NumericTerm.ValueOf(line.key()));
        Place key = within == null ? null : CardinalityComposer.settled(within,
                new NumericTerm.ValueOf(line.key()));
        RuleReadingSource ruleSource = reading.source();
        if (orders == null || keyOrders == null || key == null) {
            return linesNotWritten("`" + line.key() + "` stands at no one value, so the node the"
                    + " search stops at is not known");
        }
        if (line.matchAt().size() != 1
                || !(sourceType instanceof Type.Ref named
                        && named.name() instanceof TypeSymbol.AtModule record)
                || !(TypeView.shapeOf(sourceType, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums())
                        instanceof Shape.Product(TypeSymbol _, SequencedMap<String, Type> fields))
                || !(ruleSource.symbols().scope().reach(record)
                        instanceof TypeReachName.Written written)) {
            return linesNotWritten("the node is not a record holding the value searched for at"
                    + " one of its fields");
        }
        Type matchType = fields.get(line.matchAt().getFirst());
        Type throughType = fields.get(line.through());
        if (matchType == null || throughType == null
                || !(TypeView.shapeOf(throughType, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums()) instanceof Shape.Sequence below
                        && below.kind() == Shape.Sequence.Kind.LIST)) {
            return linesNotWritten("the nodes below a node are not a list");
        }
        Place on = keyOrders.observed().onTheGrid(key);
        if (on == null || !(namesOf(matchType, ruleSource) instanceof WornNames.Spelled)) {
            return linesNotWritten("the value searched for is not one this writes at the node");
        }
        TypeView matchView = TypeView.of(matchType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        FixtureTemplate sought = WornNames.under(matchView.wrappers(),
                FixtureTemplate.on(keyOrders.observed(), on, ruleSource.symbols().scope()::reach),
                ruleSource);
        TypeView rootView = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                wholeNumbers(asked.walking(), orders.answered(), 0, Integer.MAX_VALUE,
                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), UsualPlace.NONE),
                count -> {
                    int nodes = CountDomain.asCount(count);
                    if (nodes < 0) {
                        return new Realization.None(
                                Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                    }
                    // A chain of this many nodes holds that many elements, one below another, and
                    // is held to how many a value built here holds like any other.
                    CompositionBudget past = Witnesses.pastTheElements(nodes);
                    if (past != null) {
                        return new Realization.Stopped(CompositionShortfall.of(List.of(past)));
                    }
                    // Another value than the one searched for is wanted above the node the search
                    // stops at and for a line of none; a line of one is the node holding it alone.
                    FixtureTemplate other = nodes == 1 ? null
                            : anotherValueThan(sought, matchType, reading);
                    if (nodes != 1 && other == null) {
                        return linesNotWritten("no other value than the one searched for is there"
                                + " to write " + (nodes == 0 ? "in a tree without it"
                                        : "above the node the search stops at"));
                    }
                    FixtureTemplate chain = null;
                    CompositionShortfall met = CompositionShortfall.NONE;
                    // No line is one node that does not hold the value, with nothing below it.
                    for (int depth = Math.max(nodes, 1); depth >= 1; depth--) {
                        SequencedMap<String, FixtureTemplate> given = new LinkedHashMap<>();
                        given.put(line.matchAt().getFirst(), depth == nodes ? sought : other);
                        given.put(line.through(), FixtureTemplate.collection(
                                chain == null ? List.of() : List.of(chain)));
                        Partitions.FieldsChosen chosen = Partitions.fieldsOf(record, record,
                                reading, Set.of(), given, Partitions.RulesAround.NONE);
                        met = met.and(chosen.met());
                        if (chosen.fields() == null) {
                            return new Realization.Unexhausted(met.and(CompositionShortfall
                                    .writing(Set.of(CompositionRepertoire.TREES_WRITTEN_FOR_A_LINE))),
                                    "a node of the line is not written inside what its rules leave"
                                            + " the fields beside the two given");
                        }
                        chain = FixtureTemplate.record(written, chosen.fields());
                    }
                    return new Realization.Built(List.of(WornNames.under(rootView.wrappers(), chain,
                            ruleSource)), met);
                });
    }

    /** A value of {@code type} other than {@code sought}, or null where there is none to write. */
    private static FixtureTemplate anotherValueThan(FixtureTemplate sought, Type type,
                                                    RuleReadingContext reading) {
        return Witnesses.distinctValuesOf(type, 2, reading, Set.of()).values().stream()
                .filter(each -> !each.text().equals(sought.text())).findFirst().orElse(null);
    }

    /** A tree whose search finds a line of a given length that this does not write. */
    private static Realization linesNotWritten(String why) {
        return new Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.TREES_WRITTEN_FOR_A_LINE)), why);
    }

    /** What a tree this writes none of is said as: a population written in part. */
    private static Realization treesNotWritten(String why) {
        return new Realization.Unexhausted(CompositionShortfall.writing(
                Set.of(CompositionRepertoire.TREES_WRITTEN_FOR_A_COUNT)), why);
    }

    /**
     * Containers of the elements a key's number is gathered from, each holding elements that come
     * to one number of the set asked for.
     *
     * <p>A total is written as a total over the container is, as many elements as add up to it and
     * at least one. An end is written as one element: elements of one key whose least is a number
     * are not elements adding up to it, and one element is its own least and greatest. Either way
     * what the elements come to under their key is the number only where they share it, which the
     * row read back whole says.
     */
    private static Realization underItsKey(Type sourceType, List<List<String>> keptApart,
                                           TermOrders orders, AskedAt asked,
                                           SearchRegion within, RuleReadingContext reading,
                                           DemandsInside inside, NumericSet howMany) {
        NumericTerm.GatheredUnderItsKey gathered =
                orders.term() instanceof NumericTerm.GatheredUnderAKey ofAKey ? ofAKey.gathered()
                        : (NumericTerm.GatheredUnderItsKey) orders.term();
        if (orders.answered() == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Of the elements a statement keeps: written inside the region the statement narrows an
        // element to, every element written is kept, and what the kept ones come to is what they
        // all do. A statement no region carries is one more thing each element would have to be
        // written to meet.
        SearchRegion region = within;
        List<DemandsInside> demanded = List.of(inside);
        if (gathered.selection() != null) {
            List<TakenConstraint> kept = gathered.selection().heldTo().orElse(null);
            if (kept == null) {
                // A statement that is only which cases the element is in is asked of the element
                // as the cases it is written in, in each way it is met that stands beside what is
                // already asked inside.
                KeptOccurrences.CasesAsked ways = gathered.selection().casesAsked().orElse(null);
                List<DemandsInside> beside = new ArrayList<>();
                if (ways != null) {
                    for (Requirements way : ways.ways()) {
                        if (inside.required().merge(way)
                                instanceof Requirements.Merge.Merged(Requirements both)) {
                            beside.add(new DemandsInside(inside.among(), both));
                        }
                    }
                }
                if (beside.isEmpty()) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                demanded = beside;
            } else {
                region = TakenConstraint.narrowedBy(kept, within);
                if (TakenConstraint.nothingIsLeftFor(kept, region)) {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE);
                }
                // A text held at one value is written there in every element, as a value asked
                // inside it: an element's text is chosen by what is asked of it, and not by a
                // region.
                Map<TermPath, List<FixtureTemplate>> among = new LinkedHashMap<>(inside.among());
                for (TakenConstraint each : kept) {
                    if (each instanceof TakenConstraint.Ordered(var term, Text at, Rel rel)
                            && rel == Rel.EQ) {
                        List<FixtureTemplate> held = List.of(FixtureTemplate.string(at.at()));
                        List<FixtureTemplate> had = among.put(term.position(), held);
                        if (had != null && !had.equals(held)) {
                            return new Realization.Unexhausted(CompositionShortfall.writing(
                                    Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)),
                                    "`" + term.position() + "` is asked to hold two values");
                        }
                    }
                }
                demanded = List.of(new DemandsInside(among, inside.required()));
            }
        }
        SearchRegion keptIn = region;
        // Some element, since a key is filed where one has it: a container of none comes to
        // nought added up and files no key at all. An end is one element, which is its own end
        // by either; and how many elements the key has is asked of them as well where a count of
        // them is asked beside the number.
        // An end, and a total from the last element put, are written as one element: one element
        // is its own end, and a key whose total is its own number whichever case it is of. That
        // is a way of writing them and not what they are: a count of the key's elements that has
        // no one in it asks for one this does not write, and is not a count no key has.
        CompositionRepertoire oneElement = switch (gathered.gathering()) {
            case NumericTerm.GatheredUnderItsKey.Gathering.Total _ -> null;
            case NumericTerm.GatheredUnderItsKey.Gathering.End _ ->
                    CompositionRepertoire.ENDS_OF_A_KEY_WRITTEN_AS_ONE_ELEMENT;
            case NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut _ ->
                    CompositionRepertoire.TOTALS_FROM_A_PUT_WRITTEN_AS_ONE_ELEMENT;
        };
        NumericSet some = oneElement != null ? new NumericSet.At(Count.of(1))
                : new NumericSet.AwayFrom(List.of(Count.of(0)));
        if (oneElement != null && howMany != null && !howMany.holds(Count.of(1), Carrier.WHOLE)) {
            return new Realization.Unexhausted(CompositionShortfall.writing(Set.of(oneElement)),
                    "what the elements of a key come to is written as one element, and the key"
                            + " is asked to have more");
        }
        // A key filed in a map has some element, so whatever count of them is asked, one or more
        // of the counts in it is the size.
        ContainersAddingUp.HowManyIsAskedFor elements = new ContainersAddingUp.HowManyIsAskedFor(
                howMany == null || oneElement != null ? some : howMany, Carrier.WHOLE, 1);
        Tried tried = onTheOrder(asked.walking(), orders, asked.named(), within,
                UsualPlaces.of(orders.term(), orders.answered(), reading.today()));
        // Each way the statement is met is a row of its own, and one is no row of another: a way
        // that builds nothing says nothing of the rest.
        Realization made = firstThatBuilds(asked.walkIsOfTheWholeQuestion() && demanded.size() == 1,
                demanded, CompositionShortfall.NONE,
                heldInside -> firstThatBuilds(asked.walkIsOfTheWholeQuestion(), tried,
                        number -> ContainersAddingUp.to(number, sourceType, keptApart, orders,
                                keptIn, reading, elements, heldInside)));
        // And one that is not written is not one no row has: the container may be one its type
        // makes hold more of the key's elements than one, which it is made of.
        return oneElement != null ? someOf(made, oneElement) : made;
    }

    /**
     * Containers of the elements whose key an input holds, each element written holding that key
     * and the elements coming to one number of the set asked for, as {@link #underItsKey} writes
     * them.
     *
     * <p>The key is the row's other parameter, fixed with the rest of the row before the container
     * is composed, so the elements are written holding the one value the region leaves it at. A
     * key the region leaves at more than one is not chosen here.
     *
     * <p>Where the key is a field the number is made of, the value is not written beside the
     * share, which would be that position asked two things: the region the elements are chosen in
     * is narrowed to the key instead. What is composed is then one key of the several the number
     * is reached at, and is said to be some of them ({@link #someOfTheKeys}).
     */
    private static Realization underAKey(Type sourceType, List<List<String>> keptApart,
                                         TermOrders orders, AskedAt asked, SearchRegion within,
                                         RuleReadingContext reading, DemandsInside inside,
                                         NumericSet howMany, Place keyHeld) {
        NumericTerm.GatheredUnderAKey term = (NumericTerm.GatheredUnderAKey) orders.term();
        NumericTerm.GatheredUnderItsKey gathered = term.gathered();
        Place key = keyHeld != null ? keyHeld : within == null ? null
                : CardinalityComposer.settled(within, new NumericTerm.ValueOf(term.asked()));
        if (key == null) {
            return new Realization.Unexhausted(CompositionShortfall.writing(
                    Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)),
                    "`" + term.asked() + "` stands at no one value, so what is gathered for it is"
                            + " not known");
        }
        Carrier keyedOn = orders.fieldCarrier(term.key());
        if (keyedOn == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        TermPath keyAt = term.key().from(gathered.elements());
        // The key at a field the number is made of is the number there: every element holds the
        // key at it, so each contributes the same value and the elements come to that many of it.
        // Asked of the region, that is the run the elements are chosen in narrowed to the key; asked
        // as a value written beside the share, it would be that position asked two things.
        if (term.keyIsWhatIsAdded()) {
            Realization made = underItsKey(sourceType, keptApart, orders, asked,
                    within.given(new NumericTerm.ValueOf(keyAt), key), reading, inside, howMany);
            return someOfTheKeys(made);
        }
        List<FixtureTemplate> held = List.of(FixtureTemplate.on(keyedOn, key,
                reading.source().symbols().scope()::reach));
        Map<TermPath, List<FixtureTemplate>> among = new LinkedHashMap<>(inside.among());
        List<FixtureTemplate> had = among.put(keyAt, held);
        if (had != null && !had.equals(held)) {
            return new Realization.Unexhausted(CompositionShortfall.writing(
                    Set.of(CompositionRepertoire.ELEMENTS_CHOSEN_FOR_A_COUNT)),
                    "`" + keyAt + "` is asked to hold another value than the key");
        }
        return underItsKey(sourceType, keptApart, orders, asked, within, reading,
                new DemandsInside(among, inside.required()), howMany);
    }

    /**
     * What came of composing for a key placed at the number, said as an offer of some of the keys
     * there are: the key was one value of the several the number is reached at, so a row not
     * written is not a row there is none of.
     */
    private static Realization someOfTheKeys(Realization made) {
        return someOf(made, CompositionRepertoire.KEYS_PLACED_AT_THE_NUMBER_THEIR_ELEMENTS_COME_TO);
    }

    /**
     * {@code made} said to be an offer of some of a population {@code population} names and not
     * all of it: the nothing it came to is a nothing this tried, and never that none exists.
     */
    private static Realization someOf(Realization made, CompositionRepertoire population) {
        CompositionShortfall some = CompositionShortfall.writing(Set.of(population));
        return switch (made) {
            case Realization.Built built -> new Realization.Built(built.values(),
                    built.rest().and(some));
            case Realization.Stopped stopped -> new Realization.Stopped(stopped.met().and(some));
            case Realization.Unexhausted unexhausted -> new Realization.Unexhausted(
                    unexhausted.met().and(some), unexhausted.detail());
            case Realization.None none -> new Realization.Unexhausted(some, none.detail());
            case Realization.NoNumberTheDeclarationsAdmit nothing -> nothing;
        };
    }

    /** A container whose elements come to one of those numbers, which is what a row has to hold for
     *  this number to be there, held by a value whose rules keep its elements apart at
     *  {@code keptApart}. */
    private static Realization addingUp(AskedAt asked, Type sourceType,
                                        List<List<String>> keptApart, TermOrders orders,
                                        SearchRegion within,
                                        RuleReadingContext reading, DemandsInside inside) {
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
                onTheOrder(asked.walking(), orders, asked.named(), within,
                        UsualPlaces.of(orders.term(), orders.answered(), reading.today())),
                total -> ContainersAddingUp.to(total, sourceType, keptApart, orders, within,
                        reading, inside));
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
        // A quotient is of whole numbers, which are near nowhere in particular.
        return multipliedBackAt(by, UsualPlace.NONE, sourceType, orders, asked, within, ruleSource);
    }

    /**
     * The same, for the numbers asked for being places of an order with a usual place of its own,
     * which a step of a coarser order is: the day a date-time falls on is usually near today.
     */
    private static Realization multipliedBackAt(BigDecimal by, UsualPlace near, Type sourceType,
                                                TermOrders orders, AskedAt asked,
                                                SearchRegion within, RuleReadingSource ruleSource) {
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
                onTheOrder(asked.walking(), orders, asked.named(), within, near),
                quotient -> multipliedBack(by, sourceType, observed, quotient, ruleSource));
    }

    /**
     * A value whose remainder by that divisor is one of the numbers asked for, found by solving for
     * it ({@link RemainderSolutions}).
     *
     * <p><b>A right inverse, as the product is for a quotient.</b> Every value of a residue class
     * answers the residue; which of them to write is the one the rules leave the place, and that is
     * the member of the class nearest the end of the run, and the residue itself where the run is
     * open. What it owes is that what it writes reads back as the number it was asked for.
     */
    private static Realization atThatRemainder(BigDecimal by, Type sourceType, TermOrders orders,
                                               AskedAt asked, SearchRegion within,
                                               RuleReadingSource ruleSource) {
        Carrier observed = orders.observed();
        // A divisor that is not there, or is nought, is a term nothing built.
        if (observed == null || by == null || by.signum() == 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        NumericDomain.Bounds run = NumericDomain.Bounds.OPEN;
        switch (valueOfThePlace(orders.term(), within)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds held) -> run = held;
            case NumericDomain.FormProjection.NothingIsLeft _ -> {
                return new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            case null -> { }
        }
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                offeredBy(RemainderSolutions.solve(
                        List.of(new RemainderSolutions.Demand(by, asked.walking(), asked.named())),
                        valueOfThePlaceHeldTo(orders.term(), run, within), observed)),
                at -> writtenAt(at, sourceType, observed, ruleSource));
    }

    /** The value standing at the place {@code taking} is a number of, as far as the rules leave it:
     *  where it runs, the class the remainders fixed beside it hold it to, and whether the rules
     *  leave nothing where it stands at a number — which is how a hole is read, whatever rule made
     *  it. */
    private static RemainderSolutions.Value valueOfThePlaceHeldTo(
            NumericTerm taking, NumericDomain.Bounds run, SearchRegion within) {
        if (within == null || !(taking instanceof NumericTerm.TakenOf taken)) {
            return new RemainderSolutions.Value(run, null, at -> false);
        }
        NumericTerm.ValueOf value = new NumericTerm.ValueOf(taken.position());
        return new RemainderSolutions.Value(run,
                within.classAt(value) instanceof HeldClass.OfResidues(Congruences residues)
                        ? residues : null,
                at -> within.given(value, at).emptiness().isPresent());
    }

    /** What the rules leave of the value standing at the place {@code taking} is a number of, or
     *  null where they say nothing of it. */
    private static NumericDomain.FormProjection valueOfThePlace(NumericTerm taking,
                                                                SearchRegion within) {
        return within == null || !(taking instanceof NumericTerm.TakenOf taken) ? null
                : within.projectionOf(new NumericTerm.ValueOf(taken.position()));
    }

    /**
     * The number a solving found as the numbers to try, or none and why there are none.
     *
     * <p>A search that stopped at a figure hands over nothing and says which, which is a different
     * thing from the numbers there are being none: the first is what a reader may raise a figure for
     * and the second is a proof about the rules.
     */
    private static Tried offeredBy(RemainderSolutions.Answer answer) {
        return switch (answer) {
            case RemainderSolutions.Answer.Found(BigInteger value) ->
                    Tried.theOne(new Count(new BigDecimal(value)));
            case RemainderSolutions.Answer.NoneThere _ -> Tried.allOf(List.of());
            case RemainderSolutions.Answer.Undecided(CompositionBudget figure) ->
                    new Tried(List.of(), new Remainder.StoppedAt(figure));
        };
    }

    /**
     * The numbers of several totals tried together: a number for each, and why there are no more
     * choices of them.
     *
     * <p>Why there are no more is every reason of every walk that handed numbers over, and the
     * reason the choices of them were cut where they were: a shortfall, which adds, and not a
     * {@link Remainder}, which is one walk's single reason.
     *
     * @param each each choice of one number for every total, in the order the totals are asked
     * @param rest why there are no more choices
     */
    record Together(List<List<Place>> each, CompositionShortfall rest) {

        /**
         * Every choice of one number for each of {@code candidates}, the first total's the slowest
         * to move, up to the figure that bounds the choices.
         */
        static Together of(List<Tried> candidates) {
            int most = CompositionBudget.COMBINATIONS_OF_TOTALS_TRIED.maximum();
            CompositionShortfall left = CompositionShortfall.NONE;
            for (Tried each : candidates) {
                left = left.and(each.rest().shortfall());
            }
            List<List<Place>> out = new ArrayList<>();
            if (candidates.stream().anyMatch(each -> each.numbers().isEmpty())) {
                return new Together(out, left);
            }
            int[] at = new int[candidates.size()];
            for (boolean more = true; more; ) {
                if (out.size() == most) {
                    return new Together(out, left.and(CompositionShortfall.of(
                            Set.of(CompositionBudget.COMBINATIONS_OF_TOTALS_TRIED))));
                }
                List<Place> choice = new ArrayList<>();
                for (int i = 0; i < at.length; i++) {
                    choice.add(candidates.get(i).numbers().get(at[i]));
                }
                out.add(List.copyOf(choice));
                int i = at.length - 1;
                while (i >= 0 && ++at[i] == candidates.get(i).numbers().size()) {
                    at[i] = 0;
                    i--;
                }
                more = i >= 0;
            }
            return new Together(out, left);
        }
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
    record Tried(List<Place> numbers, Remainder rest) {

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
    sealed interface Remainder {

        /**
         * What this says to a reader as a shortfall: the one a walk met, or none where it went to
         * the end.
         *
         * <p>The one place a remainder becomes a shortfall. A remainder is one walk's reason, and
         * walks that hand over together add their shortfalls ({@link CompositionShortfall#and})
         * rather than choose among their remainders.
         */
        default CompositionShortfall shortfall() {
            return switch (this) {
                case Exhausted _ -> CompositionShortfall.NONE;
                case StoppedAt(CompositionBudget figure) -> CompositionShortfall.of(Set.of(figure));
                case SomeOf(Set<CompositionRepertoire> written) ->
                        CompositionShortfall.writing(written);
            };
        }

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
                                      int many, UsualPlace usual) {
        return wholeNumbers(wanted.extent(), at -> wanted.holds(at, on),
                BigInteger.valueOf(from), BigInteger.valueOf(to), many, usual);
    }

    /**
     * The same, of ends and a membership a caller answers rather than of one set.
     *
     * <p>For a number several sets are asked of at once: which numbers a value of the place may be
     * is every set's answer together, and no one of them is the question. The ends narrow the
     * walking and the membership decides it, which is the arrangement the single set has as well —
     * {@link NumericSet#extent()} beside {@link NumericSet#holds}.
     *
     * <p><b>Outward from where the number is usually near, where the set is left open on a
     * side.</b> The year of a date is near today's ({@link UsualPlaces}): walked up from its low end
     * instead, a set nothing bounds below gives the first year the calendar has. The walk takes the
     * place a step above before the one a step below, as every outward walk here does
     * ({@link Outwards}, {@link HeldClass#nearest}). A set a rule closed on both sides, and a number
     * with no usual place, are walked up from the low end — which is the same walk from there.
     */
    private static Tried wholeNumbers(NumericDomain.Bounds lies, Predicate<Place> holds,
                                      BigInteger from, BigInteger to, int many,
                                      UsualPlace usual) {
        // Narrowed to where the set lies before a step is taken. The window is as wide as the kind
        // of number goes, and stepping through the part of it the set is nowhere near is a walk
        // over the kind rather than a choice between the numbers the rules admit.
        //
        // Walked as whole numbers and not as decimals. A whole number has no places, so no end a
        // rule wrote to however many of them is one the step from it has to be written at.
        BigInteger first = startOf(lies.min(), from);
        BigInteger last = endOf(lies.max(), to);
        BigInteger centre = usual instanceof UsualPlace.Near near
                && near.leftOpenIn(lies.min(), lies.max())
                && Count.number(near.at()).exactly().floor() instanceof ExactAnswer.Held<BigInteger> at
                ? at.value().max(first).min(last) : first;
        List<Place> out = new ArrayList<>();
        // One past what is handed over, so that a window holding exactly as many as the figure
        // allows is a window this walked to the end of. Stopped at the figure itself, a set of
        // exactly that many numbers comes back as a search that gave something up.
        for (BigInteger away = BigInteger.ZERO; out.size() <= many
                && (centre.add(away).compareTo(last) <= 0
                        || centre.subtract(away).compareTo(first) >= 0);
                away = away.add(BigInteger.ONE)) {
            List<BigInteger> asFar = away.signum() == 0 ? List.of(centre)
                    : List.of(centre.add(away), centre.subtract(away));
            for (BigInteger at : asFar) {
                if (first.compareTo(at) <= 0 && at.compareTo(last) <= 0 && out.size() <= many) {
                    Count place = new Count(new BigDecimal(at));
                    if (holds.test(place)) {
                        out.add(place);
                    }
                }
            }
        }
        return out.size() > many
                ? new Tried(List.copyOf(out.subList(0, many)),
                        new Remainder.StoppedAt(CompositionBudget.NUMBERS_OF_A_SET_TRIED))
                : Tried.allOf(List.copyOf(out));
    }

    /** The first whole number at or above an end, or the window's own start where the set runs
     *  past it or the exact arithmetic could not hold the edge — the same answer either way, since
     *  a start this cannot narrow is one the walk is sound to leave as wide as the window itself. */
    private static BigInteger startOf(Endpoint end, BigInteger from) {
        if (end == null || !(end.at() instanceof Count count)) {
            return from;
        }
        if (!(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger> held)) {
            return from;
        }
        BigInteger edge = held.value();
        return from.max(!end.inclusive() && ExactRatio.of(edge).compareTo(count.exactly()) == 0
                ? edge.add(BigInteger.ONE) : edge);
    }

    /** The last whole number at or below an end, or the window's own end where the set runs past
     *  it or the exact arithmetic could not hold the edge, read the same way {@link #startOf}
     *  reads it. */
    private static BigInteger endOf(Endpoint end, BigInteger to) {
        if (end == null || !(end.at() instanceof Count count)) {
            return to;
        }
        if (!(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> held)) {
            return to;
        }
        BigInteger edge = held.value();
        return to.min(!end.inclusive() && ExactRatio.of(edge).compareTo(count.exactly()) == 0
                ? edge.subtract(BigInteger.ONE) : edge);
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
     *
     * <p>A value standing for the run and not one beside a line, so near where the number is
     * usually near where the run is left open ({@link Criterion.Within#standingIn}).
     *
     * @param usual where the number is usually near ({@link UsualPlaces})
     */
    private static Tried onTheOrder(NumericSet wanted, TermOrders orders, Place named,
                                    SearchRegion within, UsualPlace usual) {
        Set<CompositionRepertoire> ofTheRun =
                Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED);
        // What the declarations leave the value on its order, and which of its values they admit:
        // a place either refuses is one every row written at it is refused at.
        NumericTerm.ValueOf value = orders.term() instanceof NumericTerm.ValueOf it && within != null
                ? it : null;
        OrderedRuns declared = value == null ? null : within.orderedRegionAt(value);
        ValueSet admits = value == null ? ValueSet.ANY : within.admittedAt(value);
        switch (wanted) {
            // A set of one number is that number, and there is nothing else it could have been —
            // and where the order the declarations leave the value holds it nowhere, the set holds
            // no value of the position at all.
            case NumericSet.At one -> {
                return declared == null || declared.admits(one.value())
                        ? Tried.theOne(one.value())
                        : new Tried(List.of(), new Remainder.Exhausted());
            }
            // Anything but the values a rule singled out. Which place beside them to try is a
            // witness somebody pays for, and what a witness may cost is named where witnesses are
            // paid for — so a caller that paid names one and this tries it. Nothing built at it is
            // an answer about that number: the set holds every other one, and none was looked at.
            case NumericSet.AwayFrom _ -> {
                return new Tried(named == null || (declared != null && !declared.admits(named))
                        ? List.of() : List.of(named), new Remainder.SomeOf(ofTheRun));
            }
            // A run, with or without values taken out of it, is looked in below — in the runs the
            // set makes up, so a place a run holds is never offered for one that has it taken out.
            case NumericSet.InARun _, NumericSet.InARunExcept _ -> { }
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
        // In each run the declarations leave the value on its order, since between the ends of the
        // first and the last are gaps every alternative refuses. Where the rules leave the number
        // room and the declarations' runs hold nothing of it, the declarations leave no value
        // there, which they say.
        List<NumericDomain.Bounds> runs = LevelRealizer.runsOf(leaves, declared);
        if (runs.isEmpty()) {
            return new Tried(List.of(), new Remainder.Exhausted());
        }
        // A value held to a class is a value of the class, so what is offered are its members: the
        // end of a run is one only by luck, and a place the class refuses is no candidate whatever
        // else is asked of it afterwards.
        HeldClass members = value == null ? HeldClass.NONE : within.classAt(value);
        if (!(members instanceof HeldClass.None)) {
            return membersOnTheOrder(wanted, orders, members, runs, admits, ofTheRun, usual);
        }
        // One place of each run of the set inside each of those, standing for it — and where the
        // one standing for it is a value the position's values refuse, one of the run they take,
        // found among what the set and the order have in hand: the place standing for a run is
        // chosen by where the number is usually near, and a rule singling a value out may single
        // out that one. No machine is built for it, which a witness's own writer pays for. Where
        // the order names no place for a run, nothing is put in its stead: an order declines on
        // purpose, as above a string a rule stops short of, where every value would carry a
        // character nobody wrote.
        Carrier carrier = orders.answered();
        LevelSpace space = LevelSpace.onACarrier(carrier);
        List<Place> offered = new ArrayList<>();
        for (NumericDomain.Bounds run : runs) {
            for (LevelInterval look : Criterion.Within.runsInside(wanted.region(carrier), carrier,
                    run == null ? null : run.min(), run == null ? null : run.max())) {
                if (!(space.standingFor(look, usual).level() instanceof Level.OnACarrier on)) {
                    continue;
                }
                Place found = carrier.admitted(admits, on.at()) ? on.at()
                        : takenInstead(look, carrier, admits, on.at());
                if (!offered.contains(found)) {
                    offered.add(found);
                }
            }
        }
        return new Tried(List.copyOf(offered), new Remainder.SomeOf(ofTheRun));
    }

    /**
     * A place of {@code look} the position's values take in, found without a machine — or
     * {@code refused} where none is in hand, which the row built at it is then refused at as it
     * would have been.
     */
    private static Place takenInstead(LevelInterval look, Carrier carrier, ValueSet admits,
                                      Place refused) {
        OrderedInterval run = LevelRealizer.runOf(look, carrier);
        Place taken = run == null ? null
                : carrier.somewhereInHand(admits, run, PlacesApart.NONE);
        return taken != null ? taken : refused;
    }

    /**
     * The members of {@code members} that the runs of {@code wanted} hold inside each of
     * {@code leaves} and that the position's values take in, nearest the end the search starts
     * from, run by run.
     *
     * <p>More than one, so that what is refused of the first is not the end of the search: the next
     * member is the one a caller reads back and tries. A run holding more than are offered says so,
     * for the figure it was cut at.
     *
     * @param leaves the runs the declarations and the region leave the number, lowest first
     */
    private static Tried membersOnTheOrder(NumericSet wanted, TermOrders orders,
                                           HeldClass members, List<NumericDomain.Bounds> leaves,
                                           ValueSet admits, Set<CompositionRepertoire> ofTheRun,
                                           UsualPlace usual) {
        Carrier carrier = orders.answered();
        List<Place> offered = new ArrayList<>();
        boolean more = false;
        for (NumericDomain.Bounds within : leaves) {
            for (LevelInterval look : Criterion.Within.runsInside(wanted.region(carrier), carrier,
                    within == null ? null : within.min(), within == null ? null : within.max())) {
                OrderedInterval run = LevelRealizer.runOf(look, carrier);
                if (run == null) {
                    continue;
                }
                ClassMembers inside = members.standingIn(
                        new NumericDomain.Bounds(run.low(), run.high()), carrier, usual,
                        CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED.maximum());
                for (Place each : inside.notApart(PlacesApart.NONE)) {
                    if (carrier.admitted(admits, each)) {
                        offered.add(each);
                    }
                }
                more |= inside.stoppedShort();
            }
        }
        return new Tried(offered, more
                ? new Remainder.StoppedAt(CompositionBudget.VALUES_OF_AN_UNBOUNDED_PROGRESSION_TRIED)
                : new Remainder.SomeOf(ofTheRun));
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
        // The window is the whole numbers the run's own ends round out to. Where an end rounds to
        // no whole number the host holds, there is no window to step through, and the run is
        // looked in the way one open at that end is.
        if (lies.min() != null && lies.max() != null
                && within.min().at() instanceof Count low
                && within.max().at() instanceof Count high
                && low.exactly().floor() instanceof ExactAnswer.Held<BigInteger> from
                && high.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger> to) {
            return wholeNumbers(within, holds, from.value(), to.value(),
                    CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), UsualPlace.NONE);
        }
        Place found = on.aPlaceInside(lies.min(), lies.max(), UsualPlace.NONE);
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
                                                 SequencedMap<RealizationTarget.OfANumber,
                                                         BigDecimal> by,
                                                 SequencedMap<RealizationTarget, AskedAt> asked,
                                                 Carrier observed) {
        if (!(at instanceof Count count)) {
            return false;
        }
        for (Map.Entry<RealizationTarget.OfANumber, BigDecimal> each : by.entrySet()) {
            AskedAt of = asked.get(each.getKey());
            NumericSet wanted = of == null ? null : of.walking();
            // A candidate whose quotient the exact arithmetic could not hold is one this cannot say
            // reads back into what was asked, so it is not offered: fewer rows, and never a row at
            // a number nobody checked.
            if (!(Arithmetic.ATruncatingQuotient.quotientOf(count.at(), each.getValue())
                    instanceof ExactAnswer.Held<BigDecimal> read)) {
                return false;
            }
            Place quotient = observed.onTheGrid(new Count(read.value()));
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
        if (!(end.at() instanceof Count count)
                || !(count.exactly().ceiling() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        BigInteger quotient = startOf(end, edge.value());
        ExactRatio s = ExactRatio.of(size);
        ExactAnswer<ExactRatio> at;
        if (quotient.signum() < 0) {
            at = ExactRatio.of(quotient).times(s)
                    .flatMap(scaled -> scaled.minus(s))
                    .flatMap(below -> below.plus(ExactRatio.ONE));
        } else if (quotient.signum() == 0) {
            at = s.negated().plus(ExactRatio.ONE);
        } else {
            at = ExactRatio.of(quotient).times(s);
        }
        return placeAt(at);
    }

    /** The largest number whose quotient by {@code size} is at or below that end, read as exactly
     *  as the smallest is at the other. */
    private static Place highestWhoseQuotientIs(Endpoint end, BigDecimal size) {
        if (!(end.at() instanceof Count count)
                || !(count.exactly().floor() instanceof ExactAnswer.Held<BigInteger> edge)) {
            return null;
        }
        BigInteger quotient = endOf(end, edge.value());
        ExactRatio s = ExactRatio.of(size);
        ExactAnswer<ExactRatio> at;
        if (quotient.signum() > 0) {
            at = ExactRatio.of(quotient).times(s)
                    .flatMap(scaled -> scaled.plus(s))
                    .flatMap(above -> above.minus(ExactRatio.ONE));
        } else if (quotient.signum() == 0) {
            at = s.minus(ExactRatio.ONE);
        } else {
            at = ExactRatio.of(quotient).times(s);
        }
        return placeAt(at);
    }

    /** The number an exact ratio comes to, or null where the exact arithmetic could not hold it or
     *  where what it holds is one no written decimal is. Read the way every end of a run of
     *  quotients this file works out is read: an end too far out for the truth is work nobody asked
     *  for, and a value neither of the two ways this holds a number is one no row can write either
     *  way. */
    private static Place placeAt(ExactAnswer<ExactRatio> at) {
        if (!(at instanceof ExactAnswer.Held<ExactRatio> held)) {
            return null;
        }
        // And no more composed where the host has no room to write the number out: an end too far
        // out for the truth is the same work nobody asked for.
        return switch (held.value().writtenDecimal()) {
            case ExactAnswer.Held<Optional<BigDecimal>> written ->
                    written.value().map(Count::new).orElse(null);
            case ExactAnswer.Unheld<Optional<BigDecimal>> _ -> null;
        };
    }

    /** The one value whose quotient by that divisor is exactly that number, or nothing composed
     *  where the exact arithmetic could not hold the product. */
    private static Realization multipliedBack(BigDecimal by, Type sourceType, Carrier observed,
                                              Place answer, RuleReadingSource ruleSource) {
        if (!(answer instanceof Count wanted)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Nothing composed where the product is one the host has no room to write out, as where the
        // arithmetic could not hold it or no decimal is it.
        BigDecimal at = switch (wanted.exactly().times(ExactRatio.of(by))
                .flatMap(ExactRatio::writtenDecimal)) {
            case ExactAnswer.Held<Optional<BigDecimal>> written -> written.value().orElse(null);
            case ExactAnswer.Unheld<Optional<BigDecimal>> _ -> null;
        };
        if (at == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return writtenAt(new Count(at), sourceType, observed, ruleSource);
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
                                        List<List<String>> keptApart,
                                        TermOrders orders, AskedAt asked,
                                        SearchRegion within,
                                        RuleReadingContext reading, DemandsInside inside) {
        return switch (how) {
            case TakenAs.TheSumOfWhatItHolds _ -> addingUp(asked, sourceType, keptApart, orders,
                    within, reading, inside);
            case TakenAs.HowManyItHolds _ -> counting(asked, sourceType, keptApart, orders, within,
                    reading, inside);
            case TakenAs.PartOfTime _, TakenAs.PartOfDate _,
                    TakenAs.TheTruncatingQuotient _, TakenAs.TheFloorRemainder _ -> {
                nothingInside(inside);
                yield new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
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
    private static Realization holding(Type sourceType, List<List<String>> keptApart,
                                       AskedAt asked, TermOrders orders, SearchRegion within,
                                       RuleReadingContext reading) {
        ElementsHeldTo heldTo = new ElementsHeldTo(orders.term().subjectPath(), within);
        // From none upward, which is as far as a count runs and as many of them as the figure
        // allows. A count is the one account whose numbers are whole and whose window is the whole
        // of what it can be asked for, so a walk that reaches the end of it has walked the set.
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                wholeNumbers(asked.walking(), orders.answered(), 0, Integer.MAX_VALUE,
                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), UsualPlace.NONE),
                count -> holdingExactly(sourceType, keptApart, count, heldTo, reading));
    }

    /**
     * What the way leaves a number of each element of a container, which the elements it is
     * composed with are held to.
     *
     * <p>A condition that every element meets something is a bound on the elements and not a
     * value of one of them ({@link Generator.ElementBound}); the region carries it as what is left
     * of the element's numbers, and a container composed by its size would otherwise write
     * elements the region has no say in.
     *
     * @param container the container, which the elements are inside
     * @param within    what the way leaves, or null where it is not asked
     */
    private record ElementsHeldTo(TermPath container, SearchRegion within) {

        static final ElementsHeldTo NOTHING = new ElementsHeldTo(null, null);

        /**
         * The container of elements written inside what the way leaves their fields, in place of
         * {@code seeds}: the elements {@code seeds} hold are written from the type alone, and a
         * container holding them is no container the way asks for.
         *
         * <p>{@code seeds} stand where the way bounds no field of the element, the element is no
         * record, or the elements are kept apart or are in a set. And they stand where no element
         * could be composed inside the bounds, with what that composing met beside what building
         * them did: the offer is then short of the way, and says so.
         *
         * <p>Only of a container a parameter roots. A container inside an element of another is
         * the element's own, and the bounds the way puts on elements are on those of the container
         * a condition names; the region has no answer for a position under an element of it.
         */
        Proposals over(Proposals seeds, TypeView holder, int many, List<List<String>> keptApart,
                       RuleReadingContext reading) {
            if (container == null || within == null || !keptApart.isEmpty()
                    || container.insideAContainer()
                    || !(holder.shape() instanceof Shape.Sequence carrier)
                    || carrier.kind() != Shape.Sequence.Kind.LIST
                    || !(carrier.element() instanceof Type.Ref ref)
                    || !(ref.name() instanceof TypeSymbol.AtModule record)) {
                return seeds;
            }
            Map<String, NumericDomain.Bounds> held =
                    Partitions.leftTheFieldsOfAnElement(record, container, within, reading);
            if (held.isEmpty()) {
                return seeds;
            }
            Proposals element = Partitions.composedHeldTo(record,
                    Partitions.rulesOver(carrier.element(), record, reading.source()), reading,
                    held);
            if (element.isEmpty()) {
                return seeds.meeting(element.met());
            }
            List<FixtureTemplate> elements = new ArrayList<>();
            for (int i = 0; i < many; i++) {
                elements.add(element.values().getFirst());
            }
            return Proposals.of(List.of(FixtureTemplate.collection(elements)))
                    .meeting(seeds.met().and(element.met()));
        }
    }

    /**
     * Strings holding that many code points of a class, for each number of the set asked for.
     *
     * <p>From none upward, as every count is offered. A string holds as many of the class as it is
     * written to, so there is a string for every number and what limits the walk is the figure the
     * counts are walked under.
     */
    private static Realization holdingThatManyOfAClass(CodePointClass counted,
                                                       CaseMapping through, Type sourceType,
                                                       AskedAt asked, TermOrders orders,
                                                       RuleReadingContext reading) {
        return firstThatBuilds(asked.walkIsOfTheWholeQuestion(),
                wholeNumbers(asked.walking(), orders.answered(), 0, Integer.MAX_VALUE,
                        CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), UsualPlace.NONE),
                count -> stringsHoldingThatManyOf(counted, through, sourceType, count, reading));
    }

    /**
     * Strings of the position holding exactly {@code answer} code points of {@code counted} in
     * what {@code through} makes of them, each of them read back before it is offered.
     *
     * <p>What the type admits first and what is plainly written after, as a string of a length is
     * offered ({@link Witnesses}). What is offered is what reads back as the number asked for and
     * nothing else: a string the type admits that holds another number is a string for another
     * number, and is left out rather than offered at this one. Read back through the conversion,
     * so a string written for a class is offered for it only where the run time's answer holds
     * that many.
     */
    private static Realization stringsHoldingThatManyOf(CodePointClass counted,
                                                        CaseMapping through, Type sourceType,
                                                        Place answer, RuleReadingContext reading) {
        int many = CountDomain.asCount(answer);
        if (many < 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        RuleReadingSource ruleSource = reading.source();
        WornNames wears = namesOf(sourceType, ruleSource);
        if (!(wears instanceof WornNames.Spelled worn)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    ((WornNames.Unwritable) wears).why());
        }
        TypeView holder = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        Set<String> candidates = new LinkedHashSet<>(
                admittedStrings(holder, reading, lengthsFrom(many)));
        candidates.addAll(plainStringsHolding(counted, many));
        Set<String> held = readBackAs(counted, through, many, candidates);
        // The plain letters come first, and a conversion can make them into code points of no
        // class that is asked for; the code points it leaves as they are are tried then.
        if (held.isEmpty() && !through.equals(CaseMapping.NONE)) {
            held = readBackAs(counted, through, many, leftAsTheyAre(counted, through, many));
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (String each : held) {
            out.add(RepresentativeSource.under(worn.names(), FixtureTemplate.string(each)));
        }
        if (out.isEmpty()) {
            // Written by the class's own code points, which a conversion can make into others,
            // so the strings tried are some of the strings there are and not all of them.
            return through.equals(CaseMapping.NONE)
                    ? new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Realization.Unexhausted(CompositionShortfall.writing(Set.of(
                            CompositionRepertoire.STRINGS_A_CASE_CONVERSION_IS_WRITTEN_FOR)),
                            null);
        }
        return Realization.Built.whole(out);
    }

    /** The candidates, as the language holds them, that hold {@code many} code points of
     *  {@code counted} in what {@code through} makes of them. */
    private static Set<String> readBackAs(CodePointClass counted, CaseMapping through, int many,
                                          Collection<String> candidates) {
        Set<String> held = new LinkedHashSet<>();
        for (String each : candidates) {
            String text = asTheLanguageHoldsIt(each);
            if (text != null && countIn(counted, through, text) == many) {
                held.add(text);
            }
        }
        return held;
    }

    /**
     * Strings of {@code many} ASCII code points of {@code counted} that {@code through} leaves as
     * they are, one string for each such code point: the strings a conversion keeps the count of
     * wherever the class is written with them, whichever of them the plain letters come first by.
     */
    private static List<String> leftAsTheyAre(CodePointClass counted, CaseMapping through,
                                              int many) {
        List<String> out = new ArrayList<>();
        for (int member = 0x21; member < 0x7F; member++) {
            String own = Character.toString(member);
            if (counted.contains(member) && own.equals(BoundUnderEvaluation.mapped(through, own))) {
                out.add(own.repeat(many));
            }
        }
        return out;
    }

    /**
     * Whether every whole number from nought up is how many code points of {@code counted}
     * {@code through} makes of some string. As it stands, a string of that many of one of them is
     * one. Converted, it is where one of the ASCII code points the class counts is left as it is,
     * since a string of that many of it is made into itself: an ASCII code point is converted
     * alone and composes with none beside it.
     */
    static boolean writesEveryCountOf(CodePointClass counted, CaseMapping through) {
        if (through.equals(CaseMapping.NONE)) {
            return true;
        }
        for (int member = 0; member <= 0x7F; member++) {
            String own = Character.toString(member);
            if (counted.contains(member) && own.equals(BoundUnderEvaluation.mapped(through, own))) {
                return true;
            }
        }
        return false;
    }

    /**
     * The lengths a string the type admits is looked for at, for a string holding {@code least}
     * code points of a class: that many, which is as short as it can be, and a few more, for the
     * whitespace and separators that stand beside them.
     */
    private static List<Integer> lengthsFrom(int least) {
        int longest = least
                + CompositionBudget.CODE_POINTS_BEYOND_A_COUNT_A_STRING_IS_LOOKED_FOR.maximum();
        List<Integer> out = new ArrayList<>();
        for (int length = least; length <= longest; length++) {
            out.add(length);
        }
        return out;
    }

    /**
     * The strings of those lengths that the rules on the position admit, as text, in the order the
     * lengths are given.
     *
     * <p>The one place a string the type admits is asked for, whichever number of a string is being
     * written: a string answering a count or several of them is first of all a string of its type,
     * and a writer that chose its strings apart from this would offer ones the type refuses where
     * another would have offered ones it accepts.
     */
    private static List<String> admittedStrings(TypeView holder, RuleReadingContext reading,
                                                Collection<Integer> lengths) {
        List<String> out = new ArrayList<>();
        for (FixtureTemplate each : Partitions.admittedStringsOfSizes(holder, reading, lengths)) {
            if (each.value() instanceof Hir.StringLit written) {
                out.add(written.value());
            }
        }
        return out;
    }

    /**
     * For each of {@code sums}, a string the rules on {@code holder} leave whose code points come
     * to it, of a length every length asked admits, and holding at each index a code point is
     * asked at one of the code points tried there.
     *
     * <p>Looked for among the strings the rules leave rather than written and moved, since a string
     * of a format is made of the code points the format places, and moving one of them to reach a
     * sum writes one the format refuses. Every index asked is asked of the one string, so a string
     * holding them is written once for all of them. Each is a proposal like the others, read back
     * against every demand by whoever adopts it. Each sum is looked for in {@code steps}, and one
     * that ran out of them is said, since a sum whose string was not found is not a sum with none.
     */
    private static LeftComingTo leftComingTo(TypeView holder, RuleReadingContext reading,
                                             List<OfAString> wanted, List<Long> sums,
                                             int steps) {
        Map<Integer, CodePoints> at = new LinkedHashMap<>();
        boolean asksASum = false;
        for (OfAString each : wanted) {
            switch (each.number()) {
                case NumberOfAString.At point -> {
                    CodePoints tried = CodePoints.NONE;
                    for (Place one : each.tried().numbers()) {
                        if (one instanceof Count count && count.whole()
                                && count.exactly().floor() instanceof ExactAnswer.Held<BigInteger>(
                                        BigInteger value)
                                && value.signum() >= 0
                                && value.compareTo(BigInteger.valueOf(CodePoints.LAST)) <= 0
                                && !CodePoints.isSurrogate(value.intValue())) {
                            tried = tried.or(CodePoints.of(value.intValue()));
                        }
                    }
                    at.merge(point.index(), tried, CodePoints::and);
                }
                case NumberOfAString.CodePointSum _ -> asksASum = true;
                case NumberOfAString.Length _, NumberOfAString.InAClass _ -> { }
            }
        }
        if (asksASum ? sums.isEmpty() : at.isEmpty()) {
            return new LeftComingTo(List.of(), false);
        }
        Partitions.StringsTheRulesLeave left = Partitions.stringsTheRulesLeave(holder, reading);
        if (left == null) {
            return new LeftComingTo(List.of(), false);
        }
        IntPredicate lengths = length -> wanted.stream()
                .filter(each -> each.number() instanceof NumberOfAString.Length)
                .allMatch(each -> each.holds().test(Count.of(length)));
        List<String> out = new ArrayList<>();
        boolean pastTheWork = false;
        List<Long> each = new ArrayList<>(asksASum ? sums : List.of());
        if (!asksASum) {
            each.add(null);
        }
        for (Long sum : each) {
            switch (left.leaves().holding(at, sum, lengths, Integer.MAX_VALUE - 1, READABLE,
                    steps)) {
                case Language.ComingTo.Written(String text) -> out.add(text);
                case Language.ComingTo.NoneDoes _ -> { }
                case Language.ComingTo.PastTheWork _ -> pastTheWork = true;
            }
        }
        return new LeftComingTo(out, pastTheWork);
    }

    /** The strings the rules leave that came to the sums, and whether looking for one ran out of
     *  the steps it was given. */
    private record LeftComingTo(List<String> found, boolean pastTheWork) {}

    /**
     * Strings written for the number alone: {@code many} code points of the class, and the ones
     * that stand beside them where nothing is written — whitespace where the class does not count
     * it, and the separator the class leaves out. Each is a string some value holds, and none is
     * claimed to be the only one.
     */
    private static List<String> plainStringsHolding(CodePointClass counted, int many) {
        boolean spaceCounted = counted.contains(' ');
        List<String> out = new ArrayList<>();
        // A string of none is offered as whitespace before it is offered as nothing: a row at
        // nothing is a row that passes with whatever trimming did to it.
        if (many == 0 && !spaceCounted) {
            out.add(" ");
        }
        for (int member : writtenFor(counted.held())) {
            String held = new String(Character.toChars(member)).repeat(many);
            out.add(held);
            if (!spaceCounted) {
                out.add(held + " ");
            }
            if (counted instanceof CodePointClass.NotWhitespaceNorEqualTo(int separator)) {
                out.add(held + new String(Character.toChars(separator)));
                out.add(held + new String(Character.toChars(separator)) + " ");
            }
        }
        return out;
    }

    /**
     * The code points of {@code held} a string is written with, the first preferred: the space
     * where it is one of them; and otherwise the first plain letter there is in the set and the
     * first ideograph of the block that has no gaps — or, where it holds neither, the least of it.
     *
     * <p>Chosen from inside the set rather than from a list written for the purpose, so that no
     * set — however many separators a model writes for one string — leaves nothing to choose. The
     * letter is first since a row is read by a person. The ideograph is there for the string the
     * letter cannot be written into: a letter beside a combining separator is one code point once
     * the text is let in, and no primary composite is made of an ideograph and a mark, so a string
     * written with it keeps its code points.
     */
    private static List<Integer> writtenFor(CodePoints held) {
        if (held.has(' ')) {
            return List.of((int) ' ');
        }
        List<Integer> out = new ArrayList<>();
        PLAIN_LETTERS_FIRST.codePoints().filter(held::has).findFirst().ifPresent(out::add);
        for (char each = FIRST_IDEOGRAPH; each <= LAST_IDEOGRAPH; each++) {
            if (held.has(each)) {
                out.add((int) each);
                break;
            }
        }
        if (out.isEmpty() && !held.isEmpty()) {
            out.add(held.least());
        }
        return List.copyOf(out);
    }

    /**
     * One kind of code point a string is written with: the code points standing in exactly the
     * same classes, and the ones of them it is written with, the first preferred.
     */
    private record KindOfCodePoint(CodePoints held, List<Integer> writtenWith) {

        /** The least code point of the kind, which is the least a code point of it adds. */
        long least() {
            return held.least();
        }

        /** The greatest code point of the kind, which is the most a code point of it adds. */
        long most() {
            return held.ranges().getLast().to();
        }
    }

    /**
     * The kinds of code point a string holding the numbers {@code wanted} asks of it is written
     * with: the code points told apart by every class counted and by being whitespace, which
     * stands apart even where no class counts it. In the order a string is written in — what most
     * classes count first, whitespace last, and the rest by the first class, in the order they
     * were asked for, that leaves it out.
     */
    private static List<KindOfCodePoint> kindsOfCodePoint(List<OfAString> wanted) {
        List<CodePoints> by = new ArrayList<>();
        by.add(new CodePointClass.NotWhitespace().held());
        for (OfAString each : wanted) {
            if (each.number() instanceof NumberOfAString.InAClass(CodePointClass counted, var _)
                    && !by.contains(counted.held())) {
                by.add(counted.held());
            }
        }
        List<CodePoints> ordered = new ArrayList<>(CodePointClass.toldApart(by));
        ordered.sort(Comparator.comparing((CodePoints cell) -> !by.getFirst().has(cell.least()))
                .thenComparingInt(cell -> firstLeavingOut(by, cell)));
        List<KindOfCodePoint> out = new ArrayList<>();
        for (CodePoints cell : ordered) {
            out.add(new KindOfCodePoint(cell, writtenFor(cell)));
        }
        return out;
    }

    /** Where in {@code by} the first set leaving out the code points of {@code cell} stands, or
     *  -1 where every one of them holds them. */
    private static int firstLeavingOut(List<CodePoints> by, CodePoints cell) {
        for (int at = 0; at < by.size(); at++) {
            if (!by.get(at).has(cell.least())) {
                return at;
            }
        }
        return -1;
    }

    /**
     * {@code text} as the language holds it, which is the text a row written from it reads as, or
     * null where no {@code String} is that text.
     *
     * <p>The one place a string this composes becomes the string it offers. Text is canonicalized
     * when it is let in, so a string made of code points laid side by side — a letter and the
     * combining mark after it — is not the string the row spelled with them reads back as: it is
     * the composite, one code point where two were laid. Every count, every length and every
     * string offered is of the text as held, so a number read here is the number the row has.
     */
    private static String asTheLanguageHoldsIt(String text) {
        return BoundUnderEvaluation.heldAs(text);
    }

    /** The letters a row is written with, in the order they are preferred. */
    private static final String PLAIN_LETTERS_FIRST =
            "xyzabcdefghijklmnopqrstuvwXYZABCDEFGHIJKLMNOPQRSTUVW";

    /** The block of unified ideographs, which every code point of is assigned and none is
     *  whitespace. */
    private static final char FIRST_IDEOGRAPH = '一';

    private static final char LAST_IDEOGRAPH = '鿿';

    /** How many code points of {@code text} are in the class: the number a reading of the string
     *  comes to, which is what a string offered for a count is held to. */
    private static long countIn(CodePointClass counted, String text) {
        return text.codePoints().filter(counted::contains).count();
    }

    /** The same, of what {@code through} makes of {@code text}: -1 where the run time has no
     *  answer for it, which is a count no string is offered for. */
    private static long countIn(CodePointClass counted, CaseMapping through, String text) {
        String made = BoundUnderEvaluation.mapped(through, text);
        return made == null ? -1 : countIn(counted, made);
    }

    /** One number of a string asked for, with where it may be: what the demand admits and what the
     *  rules leave of it on the way, and the ends of both together. */
    private record OfAString(NumberOfAString number, NumericDomain.Bounds lies,
                             Predicate<Place> holds, Tried tried) {}

    /**
     * Which number of a string is asked for: how long it is, how many of its code points are in a
     * class, or what they come to.
     *
     * <p>Told apart because they are not searched alike. The first two are counts: a string holds
     * as many as it is written with, and to them the code points the same classes hold are one
     * kind. What the code points come to is no count. Two code points of one kind come to two
     * numbers, so it is reached by which code points of each kind are written and not by how many.
     */
    private sealed interface NumberOfAString {

        record Length() implements NumberOfAString {}

        /** How many code points of {@code counted} what {@code through} makes of the string holds.
         *  Written by the code points of the string that the class counts, which is where it is
         *  looked for and not what it is held to: a string is offered only as the answer reads. */
        record InAClass(CodePointClass counted, CaseMapping through) implements NumberOfAString {

            /** Whether this counts the answer of a conversion. */
            boolean ofAnAnswer() {
                return !through.equals(CaseMapping.NONE);
            }
        }

        record CodePointSum() implements NumberOfAString {}

        /** The code point at {@code index} of the string's code points, counted from nought. */
        record At(int index) implements NumberOfAString {}

        /** This number of {@code text}, as the language holds it; for a code point at an index the
         *  string does not reach, a number below nought, which no demand admits. */
        default long of(String text) {
            return switch (this) {
                case Length _ -> text.codePointCount(0, text.length());
                case InAClass in -> countIn(in.counted(), in.through(), text);
                case CodePointSum _ -> text.codePoints().asLongStream().sum();
                case At at -> text.codePoints().skip(at.index()).findFirst().orElse(-1);
            };
        }

        /** Whether this counts the code points of {@code kind}, which every length does and no
         *  sum or single code point. */
        default boolean counts(KindOfCodePoint kind) {
            return switch (this) {
                case Length _ -> true;
                case InAClass in -> in.counted().contains(kind.held().least());
                case CodePointSum _, At _ -> false;
            };
        }

        /** The number of a string {@code term} is, which a group of a string's numbers holds and
         *  nothing else does. */
        static NumberOfAString of(NumericTerm term) {
            return switch (term) {
                case NumericTerm.TakenOf taken
                        when taken.takenAs() instanceof TakenAs.HowManyItHolds -> new Length();
                case NumericTerm.CodePointClassCount count ->
                        new InAClass(count.counted(), count.through());
                case NumericTerm.CodePointValueSum _ -> new CodePointSum();
                case NumericTerm.CodePointAt at -> new At(at.index());
                case NumericTerm.TakenOf _, NumericTerm.ValueOf _, NumericTerm.Multiplicity _,
                     NumericTerm.WholeUnitsOf _,
                     NumericTerm.OccurrencesOfItsValue _, NumericTerm.OccurrencesOfAKey _,
                     NumericTerm.ExtremeOfItsKey _, NumericTerm.TakenOver _,
                     NumericTerm.GatheredUnderItsKey _, NumericTerm.GatheredUnderAKey _,
                     NumericTerm.ProductOf _ ->
                        throw new IllegalStateException(
                        term + " is no number a string is written for");
            };
        }
    }

    /**
     * A string holding the numbers asked of its code points — how many of each class's, what they
     * come to — and as many in all as the length asks.
     *
     * <p>Written out of how many there are of each kind of code point: the code points standing in
     * the same classes, with whitespace a kind apart ({@link #kindsOfCodePoint}). Every count asked
     * for is a sum of those, so a string is chosen by choosing them; what the code points come to is
     * then reached by moving code points inside their kind, which leaves every count where it was.
     * What is offered is read back through the one reader before it is — a string that does not
     * answer every demand is not offered however the counts said it would.
     *
     * <p><b>None where the demands cannot all be met, and not-walked where this did not look.</b>
     * Every number a demand admits is tried when the sets are small and every kind of code point
     * is tried up to the largest of them, which is the whole of the question for counts, so a
     * search that found nothing there is a group no string answers. Where a set is larger than
     * that the search is over some numbers, and what it did not find is a string this compiler
     * did not write.
     *
     * <p>What the code points come to is held to its demand by the counts of each kind, and not by
     * numbers tried: so many code points of a kind come to no less than as many of its least and
     * no more than as many of its greatest ({@link StringSearch#reaches}). Counts whose run misses
     * every sum the demand admits are refused as a count is, and a search that refused every way
     * of writing a string so is a proof — where the length is asked, since without it a string
     * longer than any looked at could still reach the sum. Counts whose run holds a sum the moving
     * did not reach are a string this compiler did not write, since the code points are moved a
     * few of the ways there are.
     */
    static Realization stringsHoldingTheirNumbers(
            Map<RealizationTarget.OfANumber, Carrier> answeredOn, Type sourceType,
            SequencedMap<RealizationTarget, AskedAt> demands, SearchRegion within,
            RuleReadingContext reading) {
        List<OfAString> wanted = new ArrayList<>();
        for (Map.Entry<RealizationTarget.OfANumber, Carrier> entry : answeredOn.entrySet()) {
            RealizationTarget.OfANumber each = entry.getKey();
            Carrier on = entry.getValue();
            AskedAt demand = demands.get(each);
            if (on == null || demand == null) {
                return new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            NumericDomain.Bounds held = NumericDomain.Bounds.OPEN;
            switch (within == null ? null : within.projectionOf(each.term())) {
                case NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds) ->
                        held = bounds;
                case NumericDomain.FormProjection.NothingIsLeft _ -> {
                    return new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
                }
                case null -> { }
            }
            NumericSet set = demand.walking();
            // The ends the walk steps between are what the demand and the rules leave together,
            // so numbers the rules leave out are never stepped through on the way to theirs.
            NumericDomain.Bounds lies = set.extent().meet(held);
            Predicate<Place> holds = at -> set.holds(at, on) && lies.admits(at);
            NumberOfAString number = NumberOfAString.of(each.term());
            // What code points come to runs as far as a whole number does, and a count no further
            // than a string is long.
            long upTo = number instanceof NumberOfAString.CodePointSum ? Long.MAX_VALUE
                    : Integer.MAX_VALUE;
            Tried tried = wholeNumbers(lies, holds, BigInteger.ZERO,
                    BigInteger.valueOf(upTo), CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(),
                    UsualPlace.NONE);
            wanted.add(new OfAString(number, lies, holds, tried));
        }
        boolean wholeQuestion = walkIsOfTheWholeQuestion(demands.values());
        // The code points told apart by what each class counts: how many of each kind a string
        // holds.
        List<KindOfCodePoint> written = kindsOfCodePoint(wanted);
        long greatest = written.stream().mapToLong(KindOfCodePoint::most).max()
                .orElse(Character.MAX_CODE_POINT);
        boolean everyNumberTried = true;
        // The counts a string is written to have, and what its code points are moved to come to.
        List<Integer> numbers = new ArrayList<>();
        List<Long> sums = new ArrayList<>();
        boolean sumPastWhatIsWritten = false;
        for (OfAString each : wanted) {
            // A sum is held to its demand at every way of writing a string, by what the counts can
            // come to, so the sums tried are where the moving aims and not the whole question.
            everyNumberTried &= each.number() instanceof NumberOfAString.CodePointSum
                    || each.number() instanceof NumberOfAString.At
                    || each.tried().rest() instanceof Remainder.Exhausted;
            if (each.tried().numbers().isEmpty() && each.tried().rest()
                    instanceof Remainder.Exhausted) {
                return new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
            }
            // A code point at an index is no count of any kind and no sum: it is asked of the
            // string the rules leave, at its index ({@link #leftComingTo}).
            if (each.number() instanceof NumberOfAString.At) {
                continue;
            }
            for (Place each2 : each.tried().numbers()) {
                if (each.number() instanceof NumberOfAString.CodePointSum) {
                    // A whole number from nought up to the most a long holds, which is the window
                    // the sums were walked in; anything else is no sum a string is written for.
                    if (!(each2 instanceof Count count) || !count.whole() || count.signum() < 0
                            || count.at().compareTo(BigDecimal.valueOf(Long.MAX_VALUE)) > 0) {
                        continue;
                    }
                    long sum = count.at().longValue();
                    // A string coming to it holds at least this many code points, none more than
                    // the greatest any kind holds, which is a count it is written with. One longer
                    // than a string is searched for is a number this does not write.
                    long fewest = Math.ceilDiv(sum, greatest);
                    if (fewest > CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL
                            .maximum()) {
                        sumPastWhatIsWritten = true;
                        continue;
                    }
                    sums.add(sum);
                    numbers.add((int) fewest);
                    continue;
                }
                int count = CountDomain.asCount(each2);
                if (count >= 0) {
                    numbers.add(count);
                }
            }
        }
        int largest = numbers.stream().mapToInt(Integer::intValue).max().orElse(0);
        boolean pastWhatIsSearchedInFull =
                largest > CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL.maximum();
        boolean inFull = everyNumberTried && wholeQuestion && !pastWhatIsSearchedInFull;

        int kindsOfCodePoint = written.size();
        int steps = CompositionBudget.STEPS_A_SEARCH_MAY_TAKE.maximum();
        List<Integer> kinds = codePointsOfEachKind(numbers, inFull ? largest : -1,
                (int) Math.floor(Math.pow(steps, 1.0 / kindsOfCodePoint)));

        RuleReadingSource ruleSource = reading.source();
        WornNames wears = namesOf(sourceType, ruleSource);
        if (!(wears instanceof WornNames.Spelled worn)) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                    ((WornNames.Unwritable) wears).why());
        }
        StringSearch search = new StringSearch(written, wanted, sums,
                CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), steps);
        // The strings the type admits come first and are the only ones offered where any of them
        // answers every demand. Written ones stand in only where the type admits none that
        // answers, and are proposals like the rest: whether the type's construction takes them is
        // its answer to give afterwards, and a refusal there is said as that.
        TypeView holder = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
        TreeSet<Integer> lengths = new TreeSet<>(lengthsFrom(0));
        for (int each : numbers) {
            lengths.addAll(lengthsFrom(each));
        }
        for (String each : admittedStrings(holder, reading, lengths)) {
            search.adopt(each);
        }
        LeftComingTo left = leftComingTo(holder, reading, wanted, sums, steps);
        for (String each : left.found()) {
            search.adopt(each);
        }
        if (search.found().isEmpty()) {
            search.over(0, new int[kindsOfCodePoint], kinds);
        }
        if (!search.found().isEmpty()) {
            List<FixtureTemplate> out = new ArrayList<>();
            for (String each : search.found()) {
                out.add(RepresentativeSource.under(worn.names(), FixtureTemplate.string(each)));
            }
            return Realization.Built.whole(out);
        }
        // A search that looked at every way of writing a string there is, for every number the
        // demands admit, found no string: the one answer here that is about the demands and not
        // about this compiler. Every count from nought to the largest is looked at where the counts
        // tried run that far, which they do from nought without a gap, and a run starting longer
        // than the largest is still one covering it. Where what the code points come to is asked,
        // only with the length asked as well: the length bounds every kind, and a longer string is
        // one no count looked at could rule out.
        // The ways of writing a string count its code points kind by kind, which is not how the
        // answer of a conversion holds a count, so a search over them looked at no more than some
        // of the strings there are wherever one is asked.
        boolean everyWayLookedAt = inFull && kinds.size() > largest
                && wanted.stream().noneMatch(each -> each.number()
                        instanceof NumberOfAString.InAClass in && in.ofAnAnswer())
                && search.looked() < steps && !search.leftUnwritten()
                // The ways of writing a string count its code points, and say nothing of which one
                // stands at an index.
                && wanted.stream().noneMatch(each -> each.number() instanceof NumberOfAString.At)
                && (wanted.stream().noneMatch(
                        each -> each.number() instanceof NumberOfAString.CodePointSum)
                    || wanted.stream().anyMatch(
                        each -> each.number() instanceof NumberOfAString.Length));
        if (everyWayLookedAt) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        // Otherwise what was not looked at is said as what stopped the looking: the numbers of a
        // demand that were not all tried, the counts past what is searched in full, the steps the
        // search was allowed.
        CompositionShortfall met = CompositionShortfall.NONE;
        for (OfAString each : wanted) {
            met = met.and(each.tried().rest().shortfall());
        }
        if (pastWhatIsSearchedInFull || sumPastWhatIsWritten) {
            met = met.and(CompositionShortfall.of(
                    Set.of(CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL)));
        }
        if (search.looked() >= steps || (inFull && kinds.size() <= largest) || left.pastTheWork()) {
            met = met.and(CompositionShortfall.of(
                    Set.of(CompositionBudget.STEPS_A_SEARCH_MAY_TAKE)));
        }
        if (!met.figures().isEmpty()) {
            return new Realization.Stopped(met);
        }
        return new Realization.Unexhausted(met.nothing() ? CompositionShortfall.writing(Set.of(
                CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS)) : met, null);
    }

    /**
     * How many code points of one kind a string may be written with: nought, the numbers asked
     * for and the differences between them — and every whole number up to {@code upTo} where that
     * is not negative, which is every number a string of those counts can be written with.
     */
    private static List<Integer> codePointsOfEachKind(List<Integer> asked, int upTo, int most) {
        TreeSet<Integer> kinds = new TreeSet<>(List.of(0, 1, 2));
        if (upTo >= 0) {
            for (int each = 0; each <= upTo && kinds.size() < Math.max(most, 3); each++) {
                kinds.add(each);
            }
            return List.copyOf(kinds);
        }
        kinds.addAll(asked);
        for (int one : asked) {
            for (int other : asked) {
                if (one > other) {
                    kinds.add(one - other);
                }
            }
        }
        List<Integer> out = new ArrayList<>(kinds);
        return out.size() > most ? List.copyOf(out.subList(0, most)) : List.copyOf(out);
    }

    /**
     * The strings found for a group of numbers asked of one string, and how far the looking went.
     *
     * <p>Every string comes in through {@link #adopt}, whether the type offered it or this wrote it
     * out of counts: it is let in as text is, and it is kept where the text as held reads back as
     * a number every demand admits. A string kept is therefore the one a row spells, and not the
     * code points it was made of laid side by side.
     */
    private static final class StringSearch {

        private final List<KindOfCodePoint> written;
        private final List<OfAString> wanted;
        /** What the code points are moved to come to, where that is asked; none where it is not. */
        private final List<Long> sums;
        /** Whether what the code points come to is asked, which is the demands' to say and not
         *  whether any sum was tried. */
        private final boolean asksASum;
        /** Whether each number wanted counts each kind of code point, asked once. */
        private final boolean[][] countedBy;
        /** The least and the greatest sum each number wanted that is a sum admits, asked once;
         *  nothing at the others. */
        private final long[] sumFrom;
        private final long[] sumTo;
        /** The readable code points of each kind, and every code point of it: what a code point
         *  is moved among to come to a sum, asked once. */
        private final CodePoints[] readableOfEachKind;
        private final CodePoints[] heldOfEachKind;
        /** How many ways of writing a kind the kind with the most of them has. */
        private final int ways;
        private final int most;
        private final int steps;
        private final Set<String> found = new LinkedHashSet<>();
        private int looked;
        private boolean leftUnwritten;

        StringSearch(List<KindOfCodePoint> written, List<OfAString> wanted, List<Long> sums,
                     int most, int steps) {
            this.written = written;
            this.wanted = wanted;
            this.sums = List.copyOf(sums);
            this.countedBy = new boolean[wanted.size()][written.size()];
            for (int number = 0; number < wanted.size(); number++) {
                for (int kind = 0; kind < written.size(); kind++) {
                    countedBy[number][kind] =
                            wanted.get(number).number().counts(written.get(kind));
                }
            }
            this.asksASum = wanted.stream()
                    .anyMatch(each -> each.number() instanceof NumberOfAString.CodePointSum);
            this.sumFrom = new long[wanted.size()];
            this.sumTo = new long[wanted.size()];
            for (int number = 0; number < wanted.size(); number++) {
                // Clamped to the window the sums were walked in, which a demand reaching past it
                // shares the part of.
                BigInteger window = BigInteger.valueOf(Long.MAX_VALUE);
                NumericDomain.Bounds lies = wanted.get(number).lies();
                sumFrom[number] = startOf(lies.min(), BigInteger.ZERO).max(BigInteger.ZERO)
                        .min(window).longValue();
                sumTo[number] = endOf(lies.max(), window).max(BigInteger.valueOf(-1))
                        .min(window).longValue();
            }
            this.readableOfEachKind = new CodePoints[written.size()];
            this.heldOfEachKind = new CodePoints[written.size()];
            for (int kind = 0; kind < written.size() && asksASum; kind++) {
                heldOfEachKind[kind] = written.get(kind).held();
                readableOfEachKind[kind] = heldOfEachKind[kind].and(READABLE);
            }
            this.ways = written.stream().mapToInt(each -> each.writtenWith().size()).max()
                    .orElse(0);
            this.most = most;
            this.steps = steps;
        }

        Set<String> found() {
            return found;
        }

        /** How many ways of writing a string were looked at. */
        int looked() {
            return looked;
        }

        /**
         * Whether some way of writing a string was said by its counts to answer every demand and
         * no string written that way did, which is a way of writing this did not find a string
         * for, and not a way there is none.
         */
        boolean leftUnwritten() {
            return leftUnwritten;
        }

        /** Keeps {@code candidate}, as the language holds it, where it answers every demand. */
        boolean adopt(String candidate) {
            String text = asTheLanguageHoldsIt(candidate);
            if (text == null || !answersEvery(text, wanted)) {
                return false;
            }
            if (found.size() < most) {
                found.add(text);
            }
            return true;
        }

        /**
         * Every way of writing how many code points of each kind a string holds, in the order the
         * smaller counts come first, where the string they write answers every demand.
         *
         * <p>The kinds are the code points the classes tell apart ({@link #kindsOfCodePoint}). The
         * numbers are sums of the counts chosen, so most assignments are refused without a string
         * being written; one that is not is written with each code point of a kind in turn, since
         * which of them the others stand beside decides whether the text keeps the code points it
         * was written with, and is read back as the language holds it. Where what the code points
         * come to is asked, each string written is moved to come to each number asked of it
         * ({@link #comingTo}) before it is read back.
         */
        void over(int kind, int[] counts, List<Integer> kinds) {
            if (looked >= steps || found.size() >= most) {
                return;
            }
            if (kind == counts.length) {
                looked++;
                if (countsAreAdmitted(counts)) {
                    boolean adopted = false;
                    for (int way = 0; way < ways && !adopted; way++) {
                        Laid laid = laidWith(counts, written, way);
                        if (!asksASum) {
                            adopted = adopt(laid.text());
                        }
                        for (long sum : sumsFor(laid)) {
                            if (found.size() >= most) {
                                break;
                            }
                            String moved = comingTo(laid, sum, readableOfEachKind);
                            if (moved == null) {
                                moved = comingTo(laid, sum, heldOfEachKind);
                            }
                            adopted |= moved != null && adopt(moved);
                        }
                    }
                    leftUnwritten |= !adopted;
                }
                return;
            }
            for (int each : kinds) {
                counts[kind] = each;
                over(kind + 1, counts, kinds);
            }
        }

        /**
         * What the code points of {@code laid} are moved to come to: first the number each demand
         * admits nearest what they come to as laid, which moves them least, and then the numbers
         * tried of the demands. None where nothing asks it.
         */
        private Set<Long> sumsFor(Laid laid) {
            Set<Long> out = new LinkedHashSet<>();
            if (!asksASum) {
                return out;
            }
            long asLaid = Arrays.stream(laid.codePoints()).asLongStream().sum();
            for (int number = 0; number < wanted.size(); number++) {
                OfAString each = wanted.get(number);
                if (each.number() instanceof NumberOfAString.CodePointSum
                        && sumFrom[number] <= sumTo[number]) {
                    long nearest = Math.clamp(asLaid, sumFrom[number], sumTo[number]);
                    if (each.holds().test(Count.of(nearest))) {
                        out.add(nearest);
                    }
                }
            }
            out.addAll(sums);
            return out;
        }

        /**
         * Whether every number asked admits what the counts chosen come to: the length is all of
         * them, a class holds the kinds of code point it counts, and what the code points come to
         * is some sum between as many of each kind's least and as many of its greatest
         * ({@link #reaches}). Which of those sums is asked of the string once it is written.
         */
        private boolean countsAreAdmitted(int[] counts) {
            for (int number = 0; number < wanted.size(); number++) {
                if (wanted.get(number).number() instanceof NumberOfAString.CodePointSum) {
                    if (!reaches(counts, number)) {
                        return false;
                    }
                    continue;
                }
                long sum = 0;
                for (int kind = 0; kind < counts.length; kind++) {
                    if (countedBy[number][kind]) {
                        sum += counts[kind];
                    }
                }
                if (!wanted.get(number).holds().test(Count.of(sum))) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Whether a string of {@code counts} of each kind can come to some sum the {@code number}-th
         * demand admits: its code points come to no less than as many of each kind's least, and no
         * more than as many of its greatest. A string whose run misses the demand's has no code
         * points that come to it, however they are chosen, so refusing it is a proof; one whose
         * run meets it may still miss every sum, where the kinds have gaps.
         */
        private boolean reaches(int[] counts, int number) {
            long least = 0;
            long greatest = 0;
            for (int kind = 0; kind < counts.length; kind++) {
                least += counts[kind] * written.get(kind).least();
                greatest += counts[kind] * written.get(kind).most();
            }
            return least <= sumTo[number] && greatest >= sumFrom[number];
        }
    }

    /**
     * The code points of a string as they are laid, before the language holds the text, with the
     * kind each was written as.
     */
    private record Laid(int[] codePoints, int[] kinds) {

        String text() {
            return new String(codePoints, 0, codePoints.length);
        }
    }

    /** {@code counts[i]} code points of each kind in turn, each written with the {@code way}-th
     *  code point of its kind, or its last where it has fewer. */
    private static Laid laidWith(int[] counts, List<KindOfCodePoint> written, int way) {
        int length = Arrays.stream(counts).sum();
        int[] codePoints = new int[length];
        int[] kinds = new int[length];
        int at = 0;
        for (int kind = 0; kind < written.size(); kind++) {
            List<Integer> with = written.get(kind).writtenWith();
            int codePoint = with.get(Math.min(way, with.size() - 1));
            for (int each = 0; each < counts[kind]; each++, at++) {
                codePoints[at] = codePoint;
                kinds[at] = kind;
            }
        }
        return new Laid(codePoints, kinds);
    }

    /**
     * {@code laid} with one or two of its code points moved, each to another of its own kind that
     * {@code heldOfEachKind} holds, so that together they come to {@code sum} — or null where
     * moving that few does not.
     *
     * <p>Inside the kind, so every count the string was laid for stays what it was: a kind is the
     * code points every class counted holds alike. One moved first, as far as what is short; then
     * each in turn as near as its kind lets to what is still short, until nothing is, so a sum
     * past what one code point holds is reached by as many as it takes. Which is a few of the
     * strings that come to the sum and claimed to be no more, which is why a search asking for one
     * never concludes there is none.
     *
     * <p>A kind is laid as one code point side by side ({@link #laidWith}), so moving one alone
     * the first of a kind answers for every other of it.
     */
    private static String comingTo(Laid laid, long sum, CodePoints[] heldOfEachKind) {
        int[] codePoints = laid.codePoints();
        int[] kinds = laid.kinds();
        long owed = sum - Arrays.stream(codePoints).asLongStream().sum();
        if (owed == 0) {
            return laid.text();
        }
        List<Integer> firsts = new ArrayList<>();
        for (int at = 0; at < codePoints.length; at++) {
            if (at == 0 || kinds[at] != kinds[at - 1]) {
                firsts.add(at);
            }
        }
        for (int one : firsts) {
            long to = codePoints[one] + owed;
            if (writable(heldOfEachKind[kinds[one]], to)) {
                int[] moved = codePoints.clone();
                moved[one] = (int) to;
                return new String(moved, 0, moved.length);
            }
        }
        int[] moved = codePoints.clone();
        long still = owed;
        for (int at = 0; at < moved.length && still != 0; at++) {
            CodePoints held = heldOfEachKind[kinds[at]];
            long to = moved[at] + still;
            int near = writable(held, to) ? (int) to : nearestIn(held, to);
            if (near >= 0) {
                still -= near - moved[at];
                moved[at] = near;
            }
        }
        return still == 0 ? new String(moved, 0, moved.length) : null;
    }

    /** The code points a person reading a row reads as what they are, which a string coming to a
     *  sum is moved among first: the printable ones of ASCII, the space, and the ideographs of
     *  the block that has no gaps. */
    private static final CodePoints READABLE = CodePoints.between(' ', '~')
            .or(CodePoints.between(FIRST_IDEOGRAPH, LAST_IDEOGRAPH));

    /** Whether {@code held} has {@code codePoint}. A set of code points holds no surrogate, so
     *  what it has is a code point a string holds. */
    private static boolean writable(CodePoints held, long codePoint) {
        return codePoint >= 0 && codePoint <= Character.MAX_CODE_POINT
                && held.has((int) codePoint);
    }

    /** The code point of {@code held} nearest {@code wanted}, or -1 where it has none. */
    private static int nearestIn(CodePoints held, long wanted) {
        long best = -1;
        for (CodePoints.Range range : held.ranges()) {
            long at = Math.clamp(wanted, range.from(), range.to());
            if (best < 0 || Math.abs(at - wanted) < Math.abs(best - wanted)) {
                best = at;
            }
        }
        return (int) best;
    }

    /** Whether the string reads back as a number every demand admits. */
    private static boolean answersEvery(String written, List<OfAString> wanted) {
        for (OfAString each : wanted) {
            if (!each.holds().test(Count.of(each.number().of(written)))) {
                return false;
            }
        }
        return true;
    }

    /** Values of the position holding exactly that many, which is {@link Witnesses}' answer. */
    private static Realization holdingExactly(Type sourceType, List<List<String>> keptApart,
                                              Place answer, ElementsHeldTo heldTo,
                                              RuleReadingContext reading) {
        int many = CountDomain.asCount(answer);
        if (many < 0) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        RuleReadingSource ruleSource = reading.source();
        TypeView holder = TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums());
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
        Proposals built = heldTo.over(Witnesses.ofSize(holder, many, keptApart, reading, Set.of()),
                holder, many, keptApart, reading);
        if (built.isEmpty()) {
            // Read off the build that was already done. `Witnesses` keeps what it made and why it
            // stopped as two halves of one answer for exactly this — what stopped it includes what
            // stopped the values its elements were built from — and asking it again would be the
            // same decision taken twice.
            if (!built.met().figures().isEmpty()) {
                return new Realization.Stopped(built.met());
            }
            return built.met().nothing()
                    ? new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Realization.Unexhausted(built.met(), null);
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : built.values()) {
            out.add(RepresentativeSource.under(worn.names(), each));
        }
        return new Realization.Built(out, built.met());
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
     * parts of a date are not like this, and {@link #onMovedDates} is where that is answered.
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
                    0, each.getKey().many() - 1L, 1, UsualPlace.NONE).numbers();
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
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums()).wrappers(),
                FixtureTemplate.on(observed, Count.of(seconds), ruleSource.symbols().scope()::reach),
                ruleSource);
        return standing == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : Realization.Built.whole(List.of(standing));
    }

    /** A date this composed for those parts, or the reason there is none to report with.
     *
     *  @param on       the date, or null where the walk found none
     *  @param everyOne whether the walk went over every combination the parts admit, which is what
     *                  tells a calendar that has no such date from a search that stopped short */
    record Search(LocalDate on, boolean everyOne) {}

    /**
     * One part of a date asked of it, after the date was moved.
     *
     * @param part   which part is taken
     * @param moved  what the date was made into before the part was taken
     * @param wanted the numbers the rules leave that part
     */
    record DatePartAsk(TakenAs.DatePart part, DateTranslation moved, NumericSet wanted) {

        /** This ask, ready to be put to the days. */
        PutToTheDays putToTheDays(Carrier observed) {
            return switch (part) {
                case YEAR -> new PutToTheDays(this,
                        year -> wanted.holds(Count.of(year), observed), false);
                case MONTH -> tabled(MONTHS_A_YEAR_HAS, observed);
                case DAY -> tabled(DAYS_THE_LONGEST_MONTH_HAS, observed);
            };
        }

        private PutToTheDays tabled(int most, Carrier observed) {
            BitSet left = new BitSet(most + 1);
            for (int value = 1; value <= most; value++) {
                left.set(value, wanted.holds(Count.of(value), observed));
            }
            return new PutToTheDays(this, left::get, left.isEmpty());
        }
    }

    /**
     * One ask, ready to be put to the days: which values of its part the set leaves, answered at
     * once.
     *
     * <p>A month or a day of the month takes so few values that the set is asked of each of them
     * once and each day reads the answer off the table; a walk over a cycle of the calendar would
     * otherwise ask the set again at every day of four hundred years. A year runs further than a
     * table holds and is asked of the set as it is reached, which is once a year.
     *
     * @param ask           what is asked
     * @param leaves        whether the set leaves a value of the part
     * @param leavesNothing whether it leaves no value at all, which only a table can say before a
     *                      walk
     */
    record PutToTheDays(DatePartAsk ask, IntPredicate leaves, boolean leavesNothing) {

        /** Whether the date {@code day} counts to is one this admits: one the move is defined at,
         *  whose moved date has a part the rules leave. */
        boolean admits(long day) {
            DateTranslation moved = ask.moved();
            return moved.definedAt(day) && leaves.test(partOf(ask.part(), day + moved.offsetDays()));
        }

        /**
         * The days, among those after {@code from} up to {@code to}, at which this ask is answered
         * otherwise than on the day before: where the move starts or stops being defined, and where
         * the part of the moved date starts a new run at a value the set answers otherwise than the
         * value before it.
         *
         * <p>Every part starts a new run where its value moves, a day of the month every day. The
         * answer turns only where the set's answer for the new value differs from its answer for
         * the old one, and those are the days cut at, so a set that leaves one day of the month
         * cuts a month in at most three and not in thirty-one.
         */
        void cutsInto(SortedSet<Long> cuts, long from, long to) {
            DateTranslation moved = ask.moved();
            for (long edge : new long[] {moved.first(), moved.last() + 1}) {
                addIfBetween(cuts, edge, from, to);
            }
            long low = clamped(from + moved.offsetDays());
            long high = clamped(to + moved.offsetDays());
            boolean before = leaves.test(partOf(ask.part(), low));
            for (OptionalLong start = nextStartAfter(ask.part(), low);
                    start.isPresent() && start.getAsLong() <= high;
                    start = nextStartAfter(ask.part(), start.getAsLong())) {
                boolean now = leaves.test(partOf(ask.part(), start.getAsLong()));
                if (now != before) {
                    addIfBetween(cuts, start.getAsLong() - moved.offsetDays(), from, to);
                }
                before = now;
            }
        }

        private static void addIfBetween(SortedSet<Long> cuts, long day, long from, long to) {
            if (from < day && day <= to) {
                cuts.add(day);
            }
        }

        private static long clamped(long day) {
            return Math.max(LocalDate.MIN.toEpochDay(), Math.min(LocalDate.MAX.toEpochDay(), day));
        }
    }

    /**
     * The first day after {@code day} at which {@code part} starts a new run — the first of a
     * year, the first of a month, any day for the day of the month — or nothing where the calendar
     * has no such day.
     *
     * <p>Total over the calendar. A walk that makes the next year or month and then asks whether it
     * is still inside is one that makes a date the calendar does not have in the last month there
     * is; this answers nothing there, and no caller makes the successor.
     */
    private static OptionalLong nextStartAfter(TakenAs.DatePart part, long day) {
        if (day >= LocalDate.MAX.toEpochDay()) {
            return OptionalLong.empty();
        }
        return switch (part) {
            case YEAR -> {
                int year = LocalDate.ofEpochDay(day).getYear();
                yield year == LocalDate.MAX.getYear() ? OptionalLong.empty()
                        : OptionalLong.of(LocalDate.of(year + 1, 1, 1).toEpochDay());
            }
            case MONTH -> {
                LocalDate date = LocalDate.ofEpochDay(day);
                yield date.getYear() == LocalDate.MAX.getYear() && date.getMonthValue() == 12
                        ? OptionalLong.empty()
                        : OptionalLong.of(date.withDayOfMonth(1).plusMonths(1).toEpochDay());
            }
            // Every day starts a new day of its month, and which day that is needs no date made.
            case DAY -> OptionalLong.of(day + 1);
        };
    }

    /** The part of the date that {@code day} counts to, with a day the calendar does not have read
     *  as its first or last. */
    private static int partOf(TakenAs.DatePart part, long day) {
        LocalDate date = LocalDate.ofEpochDay(Math.max(LocalDate.MIN.toEpochDay(),
                Math.min(LocalDate.MAX.toEpochDay(), day)));
        return switch (part) {
            case YEAR -> date.getYear();
            case MONTH -> date.getMonthValue();
            case DAY -> date.getDayOfMonth();
        };
    }

    /**
     * A date whose parts, each after the date was moved as its own ask says, are ones the rules
     * leave.
     *
     * <p>Solved over the days and not over the parts. Every ask is a condition on the date the
     * program was given: the move is defined there, and the part of the moved date is one the rules
     * leave. What a group asks of one date is the meeting of those conditions, so a year after one
     * move, a year after another and a month with no move are one question and not three. A date
     * nobody moved is a date moved by nothing, and its parts are asked the same way.
     *
     * <p>The parts constrain each other — how far the days run depends on the month, and
     * February's length on the year — and walking the days is what keeps that the calendar's:
     * every date walked is one there is, so no combination is offered that no date has, and none
     * the calendar has is missed for want of a part nobody asked for standing where it allows it.
     * Whether a date can have a part is asked of the calendar and not of the bound the operation
     * declares, which is what the model may assume of an answer and not what a witness is built of.
     *
     * <p>The years of the first year asked for are walked, or one cycle of the calendar where no
     * year is asked for ({@link #dateAnsweringMovedParts}), and the days walked are cut where any
     * ask is answered otherwise than on the day before: between two cuts nothing the group asks
     * changes, so the first day of each is every day of it. What this walks is therefore every
     * combination there is, and an answer of nothing is a statement about the calendar.
     */
    private static Realization onMovedDates(List<DatePartAsk> asks, Type sourceType,
                                            Carrier observed, RuleReadingContext reading) {
        if (observed == null) {
            return new Realization.None(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        RuleReadingSource ruleSource = reading.source();
        Search found = dateAnsweringMovedParts(asks, observed, reading.today());
        if (found.on() == null) {
            return found.everyOne()
                    ? new Realization.None(
                            Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                    : new Realization.Stopped(CompositionShortfall.of(
                            Set.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED)));
        }
        FixtureTemplate standing = WornNames.under(
                TypeView.of(sourceType, ruleSource.inners(), ruleSource.symbols(),
                        ruleSource.kinds(), ruleSource.sums()).wrappers(),
                FixtureTemplate.on(observed, Dates.dayOf(found.on()),
                        ruleSource.symbols().scope()::reach),
                ruleSource);
        return standing == null
                ? new Realization.None(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : Realization.Built.whole(List.of(standing));
    }

    /**
     * The date nearest {@code today} that every one of {@code asks} admits, counted in years and
     * then in days.
     *
     * <p>Where a year is asked for, the years the first such ask leaves are walked outward from
     * today's, and the dates whose moved date is in one of them are a run of days.
     *
     * <p>Where none is, one cycle of the calendar is walked outward from today's year. The
     * Gregorian calendar repeats every
     * four hundred years, and those are a whole number of days, so a month or a day of a date moved
     * by a count of days is the same at every date a cycle away. Every combination the asks can
     * meet at is therefore met within one cycle of days they are all defined at, or within all of
     * those days where there are fewer than a cycle of them, and the walk is over every one there
     * is.
     */
    static Search dateAnsweringMovedParts(List<DatePartAsk> asks, Carrier observed, Today today) {
        List<PutToTheDays> put = asks.stream().map(each -> each.putToTheDays(observed)).toList();
        if (put.stream().anyMatch(PutToTheDays::leavesNothing)) {
            return new Search(null, true);
        }
        DatePartAsk lead = asks.stream().filter(each -> each.part() == TakenAs.DatePart.YEAR)
                .findFirst().orElse(null);
        if (lead == null) {
            return new Search(dateInOneCycle(put, today), true);
        }
        Tried years = wholeNumbers(lead.wanted(), observed,
                LocalDate.MIN.getYear(), LocalDate.MAX.getYear(),
                CompositionBudget.NUMBERS_OF_A_SET_TRIED.maximum(), UsualPlaces.ofAYear(today));
        boolean everyOne = years.rest() instanceof Remainder.Exhausted;
        for (Place year : years.numbers()) {
            LocalDate on = dateInTheRunOf(lead, whole(year), put);
            if (on != null) {
                return new Search(on, everyOne);
            }
        }
        return new Search(null, everyOne);
    }

    /**
     * The first date the lead ask's moved date is in {@code year} at, and every other ask admits,
     * or null where there is none.
     */
    private static LocalDate dateInTheRunOf(DatePartAsk lead, int year, List<PutToTheDays> asks) {
        DateTranslation moved = lead.moved();
        long from = Math.max(moved.first(),
                LocalDate.of(year, 1, 1).toEpochDay() - moved.offsetDays());
        long to = Math.min(moved.last(),
                LocalDate.of(year, 12, 31).toEpochDay() - moved.offsetDays());
        return from > to ? null : firstAdmittedIn(from, to, asks);
    }

    /**
     * The first date of a cycle of the calendar that every one of {@code asks} admits, or null where
     * there is none.
     *
     * <p>Which days are walked and in what order they are walked are two answers. The days are a
     * cycle with the first day of today's year at its middle where every ask is defined there, and
     * otherwise the nearest cycle that is — any day starts a cycle, and every combination the asks
     * can meet at is met within one. The order is today's year first and then the years either side of it,
     * the one after before the one before, as every outward walk here takes them: so a date the
     * asks meet in today's year is found there however near the end of the calendar today is, and
     * a twenty-ninth of February in the leap year nearest it. Each year is walked a year of the
     * date at a time, so that a date found early is found without cutting the rest of the cycle.
     */
    private static LocalDate dateInOneCycle(List<PutToTheDays> asks, Today today) {
        long first = asks.stream().mapToLong(each -> each.ask().moved().first()).max()
                .orElseThrow();
        long last = asks.stream().mapToLong(each -> each.ask().moved().last()).min()
                .orElseThrow();
        if (first > last) {
            return null;
        }
        // A cycle with today's year at its middle, so that the years either side of it are both
        // in it; moved inside the days the asks are defined at where it reaches past them.
        long from = Math.max(first, Math.min(today.firstOfItsYear() - DAYS_OF_A_CYCLE / 2,
                last - DAYS_OF_A_CYCLE + 1));
        long to = Math.min(last, from + DAYS_OF_A_CYCLE - 1);
        int earliest = LocalDate.ofEpochDay(from).getYear();
        int latest = LocalDate.ofEpochDay(to).getYear();
        int centre = Math.max(earliest, Math.min(latest, today.year()));
        for (int away = 0; centre + away <= latest || centre - away >= earliest; away++) {
            for (int year : away == 0 ? List.of(centre) : List.of(centre + away, centre - away)) {
                if (year < earliest || year > latest) {
                    continue;
                }
                long start = Math.max(from, LocalDate.of(year, 1, 1).toEpochDay());
                long end = Math.min(to, LocalDate.of(year, 12, 31).toEpochDay());
                LocalDate found = firstAdmittedIn(start, end, asks);
                if (found != null) {
                    return found;
                }
            }
        }
        return null;
    }

    /** The first date from {@code from} to {@code to} that every one of {@code asks} admits, or
     *  null where there is none. The days are a year of them or fewer, which is what keeps the cuts
     *  of a day of the month few. */
    private static LocalDate firstAdmittedIn(long from, long to, List<PutToTheDays> asks) {
        assert to - from < 366 : "a run of days walked at once is a year or less: " + from
                + " to " + to;
        // Each ask is answered the same way between two of the days it changes at, so the first
        // day of each stretch is every day of it.
        TreeSet<Long> cuts = new TreeSet<>();
        cuts.add(from);
        for (PutToTheDays each : asks) {
            each.cutsInto(cuts, from, to);
        }
        for (long day : cuts) {
            if (admitsEvery(asks, day)) {
                return LocalDate.ofEpochDay(day);
            }
        }
        return null;
    }

    private static boolean admitsEvery(List<PutToTheDays> asks, long day) {
        for (PutToTheDays each : asks) {
            if (!each.admits(day)) {
                return false;
            }
        }
        return true;
    }

    /** {@code at} as a whole number, which every {@link #wholeNumbers} search this is asked of hands
     *  back — asked anyway, since the day this reaches an {@code at} that is not one, the answer
     *  it gives is that search's contract broken, and not a {@code java.math} refusal. */
    private static int whole(Place at) {
        try {
            return ((Count) at).at().intValueExact();
        } catch (ArithmeticException notWhole) {
            throw new IllegalStateException(
                    "a place a whole-number search produced is not itself a whole number: " + at,
                    notWhole);
        }
    }

    /** How far the months run, which is what a month may stand at whatever the rules leave it. */
    private static final int MONTHS_A_YEAR_HAS = 12;

    /** How far the days run in the longest month there is, which is as far as a day of any date
     *  runs. Which of them a date has is the date's, read off it where it is walked to. */
    private static final int DAYS_THE_LONGEST_MONTH_HAS = 31;

    /** How many days the Gregorian calendar takes to repeat: four hundred years, of which ninety-seven
     *  are leap years. */
    private static final long DAYS_OF_A_CYCLE = 400L * 365 + 97;

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
                        ruleSource.kinds(), ruleSource.sums()).wrappers(), bare, ruleSource)));
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
                ruleSource.kinds(), ruleSource.sums()).wrappers(), ruleSource);
    }

    private TermRealizations() {}
}
