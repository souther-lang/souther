package souther.compiler.reading;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.flow.AWayThrough;
import souther.compiler.flow.ComparisonWays;
import souther.compiler.inputs.ComparedNumber;
import souther.compiler.inputs.ComparedNumbers;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.MeaningsOfABodyReading;
import souther.compiler.partition.WhatTheDeclarationsLeave;
import souther.compiler.partition.WhatTheDeclarationsLeaveAnArm;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Which ways a comparison has a value behind it, answered from the number it is about.
 *
 * <p>The reading a body's comparisons are admitted by. A comparison names a number of the input, the
 * rules leave that number a run of values, and a way stands where some value of that run falls on
 * the side the way needs. Nothing here reads how the comparison was written: which side the number
 * was on, whether it was a name or something taken of one, and what kind of node stands there are
 * all settled before this is asked ({@link ComparedNumber}).
 *
 * <p><b>Why that is the question.</b> Read off the shape of the operands, a comparison over a number
 * taken of a location is a call against a literal and nothing about it says a value varies — so the
 * way was never held, the decision was never named, and no row was ever steered into the arm behind
 * it. The number is what varies, and the number is what is asked about here.
 *
 * <p>The same reading the decision is named from ({@link ComparedNumbers}). Admitting a way and
 * saying which decision it settles are two questions about one comparison, and answering them from
 * two readings is how a way came to be held for a number the naming could not find.
 *
 * <p>Where the comparison draws no line — a number over a run of values, one position against
 * another, a value no order writes — the body's own text answers as it did before. That is not a
 * second answer to this question: it is the answer for the comparisons this one has nothing to say
 * about.
 */
final class NumberWays implements ComparisonWays {

    private final ComparedNumbers numbers;
    private final Quantities quantities;
    // Where this reader stands, which is its own and not the naming's. The two walk the same body
    // and meet each comparison at the same node, and the reading they share says so rather than
    // taking it on trust ({@link ComparedNumbers#of}).
    private final InputReads reads;
    private final Symbols symbols;

    /** Which declarations wear one value, which is what says whether reading a field reaches
     *  somewhere else ({@link souther.compiler.check.Location#isStep}). */
    private final DeclarationNewtypes newtypes;

    /** What each condition of the model the body holds states, read where the language's
     *  operations stand. */
    private final MeaningsOfABody meanings;

    NumberWays(ComparedNumbers numbers, Quantities quantities, InputReads reads, Symbols symbols,
               DeclarationNewtypes newtypes, MeaningsOfABody meanings) {
        this.numbers = numbers;
        this.quantities = quantities;
        this.reads = reads;
        this.symbols = symbols;
        this.newtypes = newtypes;
        this.meanings = meanings;
    }

    @Override
    public ComparisonWays entering(ScopeStep step) {
        InputReads inside = reads.entering(step, symbols, newtypes);
        return inside == reads ? this
                : new NumberWays(numbers, quantities, inside, symbols, newtypes, meanings);
    }

    /**
     * A fork of the model is entered where the input's declarations do not prove that what its
     * condition states never comes out that way ({@link WhatTheDeclarationsLeave}) — which is not a
     * proof that a value takes it. So is a fork in a copy of one of the
     * language's operations: it states nothing of the model, and what its condition states, read
     * where the copy stands, is what the operation's body says at the call
     * ({@link MeaningsOfABodyReading#ofACopiedCondition}) — read by the rules a model's conditions
     * are read by, and not by this reader on its own.
     */
    @Override
    public Optional<AWayThrough> stated(Core.If fork, boolean want) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(fork.place().occurrence());
        // A body with no reading of what its conditions mean has its forks read as they stand.
        if (meanings == MeaningsOfABody.NONE) {
            return Optional.empty();
        }
        if (construct.isEmpty()) {
            return insideACopyOfTheLibrary(fork)
                    ? Optional.of(WhatTheDeclarationsLeave.whetherRuledOut(MeaningsOfABodyReading
                            .ofACopiedCondition(fork.cond(), reads, numbers.reading()), want,
                            numbers.reading()))
                    : Optional.empty();
        }
        // One that has a reading and states nothing at this fork is not read a second way: the
        // fork is not ruled out, for the reason nothing is stated there.
        MeaningsOfABody.Site site =
                new MeaningsOfABody.Site(construct.get(), MeaningsOfABody.Part.Asked.CONDITION);
        return Optional.of(meanings.at(site)
                .map(proposition -> WhatTheDeclarationsLeave.whetherRuledOut(proposition, want,
                        numbers.reading()))
                .orElseGet(() -> new AWayThrough.NotRuledOut(List.of(
                        new WhyNotTaken.MeaningUnread(meanings.whyNothingAt(site))))));
    }

    /** Whether {@code fork} stands in a copy of one of the language's operations, the copy made
     *  where the model called it. */
    private static boolean insideACopyOfTheLibrary(Core.If fork) {
        return fork.place().occurrence().lineage() instanceof OccurrenceLineage.Expansion copy
                && copy.expanded() instanceof ValueName.Stdlib.Operation;
    }

    @Override
    public Predicate<Core.Case> mayTake(Core.Match match) {
        WhatTheDeclarationsLeaveAnArm arms = WhatTheDeclarationsLeaveAnArm.of(match, reads,
                symbols, newtypes, meanings, numbers.reading());
        return arm -> arms.ruledOut(match.cases().indexOf(arm)).isEmpty();
    }

    @Override
    public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        Core.Binary binary = Core.withoutStanding(e) instanceof Core.Binary it ? it : null;
        // A case of a sum, which the value either is or is not: no number places it, and what the
        // declarations leave of it is asked of what it states, as a fork's condition is.
        if (binary != null && numbers.caseOf(binary, reads) != null) {
            return !ruledOutAsStated(binary, want);
        }
        ComparedNumber said = binary != null ? numbers.of(binary, reads) : null;
        ComparedNumber.DrawnLine drawn = said == null ? null : said.line();
        if (drawn != null) {
            return !ruledOut(drawn, want);
        }
        PairsLeft left = said != null && said.against() != null
                ? twoPositionsComeOut(said, want) : PairsLeft.NOT_READ;
        // The declarations hold of every input, so a way they leave no pair standing is closed
        // whatever the text of the body would allow: the text reads two positions as two values
        // nothing relates.
        return switch (left) {
            case NONE -> false;
            case SOME -> true;
            case NOT_READ -> ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy);
        };
    }

    /** What the declarations leave of a way two positions stand to each other. */
    private enum PairsLeft {
        /** Some pair of values they leave stands that way. */
        SOME,
        /** No pair of values they leave does, every end read as far as it is written. */
        NONE,
        /** What they leave of the two is not read here. */
        NOT_READ
    }

    /**
     * Whether some pair of values the declarations leave two positions stands to each other the
     * way {@code said} needs to come out {@code want}.
     *
     * <p>Asked of a comparison of one position against another, which draws no line. The two run
     * where the declarations leave them, apart, and a pair stands each way the runs leave room for:
     * level where they meet, and one below the other where one reaches lower than the other reaches
     * high. Not a proof a row takes the way — what lies inside a run is more than this reads.
     *
     * <p>And the two held against each other where a rule relates them: the runs apart leave a
     * pair standing each way, and a rule that one is never past the other leaves only some of them.
     * Asked as where the difference of the two lies, which is the rule's own question. Each answer
     * reads an end as far as it is written and no further, so a sign it says no pair stands is one
     * every value it covers is strictly out of; the two together are what both leave.
     */
    private PairsLeft twoPositionsComeOut(ComparedNumber said, boolean want) {
        if (!(said.placed() instanceof ComparisonClaim claim)) {
            return PairsLeft.NOT_READ;
        }
        NumericDomain.Bounds one = quantities.runsBetween(said.term());
        NumericDomain.Bounds other = quantities.runsBetween(said.against());
        if (one == null || other == null) {
            return PairsLeft.NOT_READ;
        }
        NumericDomain.Bounds apart = differenceOf(said);
        if (apart == null) {
            return PairsLeft.NONE;
        }
        Rel needed = want ? claim.statedRelation() : claim.statedRelation().denied();        for (int sign = -1; sign <= 1; sign++) {
            if (needed.holds(sign) && standThatWay(one, other, sign)
                    && differsThatWay(apart, sign)) {
                return PairsLeft.SOME;
            }
        }
        return PairsLeft.NONE;
    }

    /**
     * Where the first position less the second lies, as the region reads every rule reaching the
     * two; null where it leaves the two no values at all. Every value there is where the
     * difference is no number counted — two strings have none — where the arithmetic could not
     * hold it, or where the region read nothing of it.
     */
    private NumericDomain.Bounds differenceOf(ComparedNumber said) {
        LinearForm<NumericTerm> form = LinearForm.atom(said.term())
                .minus(LinearForm.atom(said.against())).orNull();
        if (form == null) {
            return NumericDomain.Bounds.OPEN;
        }
        return switch (quantities.region().projectionOf(form)) {
            case NumericDomain.FormProjection.NothingIsLeft _ -> null;
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds bounds) ->
                    new NumericDomain.Bounds(counted(bounds.min()), counted(bounds.max()));
            // Nothing read of where the form lies, which rules nothing out.
            case null -> NumericDomain.Bounds.OPEN;
        };
    }

    /** {@code end} where it is a number counted, and no end where it is anything else. */
    private static Endpoint counted(Endpoint end) {
        return end != null && end.at() instanceof Count ? end : null;
    }

    /**
     * Whether a difference within {@code apart} can have the sign {@code sign}: below nothing where
     * it reaches under nothing, at nothing where nothing lies in it, above where it reaches over.
     */
    private static boolean differsThatWay(NumericDomain.Bounds apart, int sign) {
        Endpoint nothing = Endpoint.inclusive(Count.ZERO);
        return switch (Integer.signum(sign)) {
            case 0 -> notPast(apart.min(), nothing) && notPast(nothing, apart.max());
            case -1 -> below(apart.min(), nothing);
            default -> below(nothing, apart.max());
        };
    }

    /**
     * Whether a value of {@code one} and a value of {@code other} can stand {@code sign} from each
     * other: level where the runs meet, below where {@code one} starts under where {@code other}
     * ends, above the other way round. An absent end runs to the end of the order.
     */
    private static boolean standThatWay(NumericDomain.Bounds one, NumericDomain.Bounds other,
                                        int sign) {
        return switch (Integer.signum(sign)) {
            case 0 -> meet(one, other);
            case -1 -> below(one.min(), other.max());
            default -> below(other.min(), one.max());
        };
    }

    /** Whether some value lies in both runs. */
    private static boolean meet(NumericDomain.Bounds one, NumericDomain.Bounds other) {
        return notPast(one.min(), other.max()) && notPast(other.min(), one.max());
    }

    /** Whether a value at or above {@code low} lies at or below {@code high}, each taken as far as
     *  it is inclusive. */
    private static boolean notPast(Endpoint low, Endpoint high) {
        if (low == null || high == null) {
            return true;
        }
        int at = low.at().compareTo(high.at());
        return at < 0 || (at == 0 && low.inclusive() && high.inclusive());
    }

    /** Whether some value from {@code low} up stands strictly below some value up to
     *  {@code high}. */
    private static boolean below(Endpoint low, Endpoint high) {
        return low == null || high == null || low.at().compareTo(high.at()) < 0;
    }

    /**
     * Whether the declarations prove {@code comparison} never comes out {@code want}, asked of what
     * the body's meanings say it states — and nothing proved where they say nothing of it.
     *
     * <p>The statement a rule concluded and the body's meanings filed, as a fork's condition is
     * asked ({@link #stated}), so what a comparison states is the one rule's answer and what the
     * declarations leave of it is the one table's.
     */
    private boolean ruledOutAsStated(Core.Binary comparison, boolean want) {
        if (meanings == MeaningsOfABody.NONE || comparison.occurrence() == null) {
            return false;
        }
        return ModelOccurrence.statedAt(comparison.occurrence())
                .flatMap(construct -> meanings.at(new MeaningsOfABody.Site(construct,
                        MeaningsOfABody.Part.Asked.ITSELF)))
                .map(proposition -> WhatTheDeclarationsLeave.whetherRuledOut(proposition, want,
                        numbers.reading()) instanceof AWayThrough.RuledOut)
                .orElse(false);
    }

    /**
     * Whether the run the declarations leave the number proves the comparison never comes out
     * {@code want}.
     *
     * <p>The relation the way needs is the one the comparison states, or its denial where the way
     * is the other one, and what a run's ends rule out of a relation is the one table there is of it
     * ({@link WhatTheDeclarationsLeave#ruledOutByBounds}). {@link #comesOut} answers in the
     * positive, so it reads the denial of this: not ruled out, which is no proof a value comes out
     * that way.
     */
    private boolean ruledOut(ComparedNumber.DrawnLine drawn, boolean want) {
        Rel stated = drawn.claim().statedRelation();
        return WhatTheDeclarationsLeave.ruledOutByBounds(quantities.runsBetween(drawn.term()),
                want ? stated : stated.denied(), drawn.at());
    }
}
