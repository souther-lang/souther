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
import souther.compiler.inputs.Quantities;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.WhatTheRulesLeave;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;
import java.util.Set;
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
     * A fork of the model is entered where what its condition states can come out that way under
     * the input's rules ({@link WhatTheRulesLeave}). A fork in a copy of one of the language's
     * operations states nothing of the model, and its parts answer.
     */
    @Override
    public Optional<AWayThrough> stated(Core.If fork, boolean want) {
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(fork.place().occurrence());
        // A body with no reading of what its conditions mean has its forks read as they stand.
        if (construct.isEmpty() || meanings == MeaningsOfABody.NONE) {
            return Optional.empty();
        }
        // One that has a reading and states nothing at this fork is not read a second way: the
        // fork is not ruled out, for the reason nothing is stated there.
        MeaningsOfABody.Site site =
                new MeaningsOfABody.Site(construct.get(), MeaningsOfABody.Part.Asked.CONDITION);
        return Optional.of(meanings.at(site)
                .map(proposition -> WhatTheRulesLeave.admits(proposition, want,
                        numbers.reading()))
                .orElseGet(() -> new AWayThrough.NotRuledOut(List.of(
                        new WhyNotTaken.MeaningUnread(meanings.whyNothingAt(site))))));
    }

    @Override
    public Predicate<Core.Case> mayTake(Core.Match match) {
        Set<TypeSymbol> written = reads.casesWritten(match.scrutinee(), symbols, newtypes);
        if (written != null) {
            return arm -> InputReads.whetherEveryRowTakes(arm, written).orElse(true);
        }
        // Otherwise an arm is taken where what entering it states can come out true under the
        // input's rules, as a fork's condition is.
        Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(match.place().occurrence());
        if (construct.isEmpty() || meanings == MeaningsOfABody.NONE) {
            return arm -> true;
        }
        return arm -> meanings.at(new MeaningsOfABody.Site(construct.get(),
                        new MeaningsOfABody.Part.OfACase(match.cases().indexOf(arm))))
                .map(proposition -> !(WhatTheRulesLeave.admits(proposition, true,
                        numbers.reading()) instanceof AWayThrough.RuledOut))
                .orElse(true);
    }

    @Override
    public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        ComparedNumber said =
                Core.withoutStanding(e) instanceof Core.Binary binary
                        ? numbers.of(binary, reads) : null;
        ComparedNumber.DrawnLine drawn = said == null ? null : said.line();
        return drawn == null
                ? ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy)
                : leaves(drawn, want);
    }

    /** Whether the values the rules leave the number include one the comparison comes out
     *  {@code want} at. */
    private boolean leaves(ComparedNumber.DrawnLine drawn, boolean want) {
        NumericDomain.Bounds runs = quantities.runsBetween(drawn.term());
        return switch (drawn.claim()) {
            case ComparisonClaim.Cut cut -> {
                // Which side the way needs, which is the side the comparison is true on.
                boolean upIsTrue = cut.satisfyingSide() == Towards.ABOVE;
                yield WhatTheRulesLeave.anythingBeyond(runs, drawn.at(), upIsTrue == want,
                        cut.holdsAtTheValue() == want);
            }
            // The value itself where the way is the one the comparison holds at, and everything else
            // where it is the other. What is left over is empty only where the run is that one value
            // and nothing else.
            case ComparisonClaim.Singled singled -> singled.holdsAtTheValue() == want
                    ? holds(runs, drawn.at()) : notOnlyOneValue(runs, drawn.at());
        };
    }

    /** Whether the run holds the value the comparison named. */
    private static boolean holds(NumericDomain.Bounds runs, Place at) {
        return WhatTheRulesLeave.anythingBeyond(runs, at, true, true)
                && WhatTheRulesLeave.anythingBeyond(runs, at, false, true);
    }

    /** Whether the run holds anything but the value the comparison named. */
    private static boolean notOnlyOneValue(NumericDomain.Bounds runs, Place at) {
        return WhatTheRulesLeave.anythingBeyond(runs, at, true, false)
                || WhatTheRulesLeave.anythingBeyond(runs, at, false, false);
    }
}
