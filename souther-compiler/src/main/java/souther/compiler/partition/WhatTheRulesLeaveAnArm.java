package souther.compiler.partition;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.flow.AWayThrough;
import souther.compiler.flow.WhyNoValueTakesTheArm;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * Whether any value arrives at an arm of a {@code match}, decided once for every reader that asks.
 *
 * <p>Three things can show it does not, and they are weighed in this order here and nowhere else.
 * A scrutinee the source wrote is of the cases written, and an arm none of them takes is entered by
 * nothing, whatever the rules leave. Otherwise what entering the arm states ({@link
 * MeaningsOfABody}) is put to what the declarations and rules leave the input
 * ({@link WhatTheRulesLeave}), wherever the scrutinee stands: a position of the input, or a value
 * the body works out whose cases are read off the input. A body with no reading of what its arms
 * state has the one reading it has, the rules of the position the scrutinee stands at.
 *
 * <p>Not ruled out is no proof that anything arrives: it is empty here, and what a reader does with
 * an arm nothing ruled out is its own.
 */
public final class WhatTheRulesLeaveAnArm {

    private final Core.Match match;
    private final InputReads reads;
    private final DeclarationNewtypes newtypes;
    private final MeaningsOfABody meanings;
    private final InputReading read;
    private final Set<TypeSymbol> written;
    private final Optional<ModelOccurrence> construct;

    private WhatTheRulesLeaveAnArm(Core.Match match, InputReads reads, Symbols symbols,
                                   DeclarationNewtypes newtypes, MeaningsOfABody meanings,
                                   InputReading read) {
        this.match = match;
        this.reads = reads;
        this.newtypes = newtypes;
        this.meanings = meanings;
        this.read = read;
        this.written = reads.casesWritten(match.scrutinee(), symbols, newtypes);
        this.construct = ModelOccurrence.statedAt(match.place().occurrence());
    }

    /** The arms of {@code match}, read in {@code reads} against what {@code read} leaves the
     *  input. */
    public static WhatTheRulesLeaveAnArm of(Core.Match match, InputReads reads, Symbols symbols,
                                            DeclarationNewtypes newtypes,
                                            MeaningsOfABody meanings, InputReading read) {
        return new WhatTheRulesLeaveAnArm(match, reads, symbols, newtypes, meanings, read);
    }

    /** What shows no value arrives at arm {@code index}, or empty where nothing does. */
    public Optional<WhyNoValueTakesTheArm> ruledOut(int index) {
        Core.Case arm = match.cases().get(index);
        if (written != null) {
            return InputReads.whetherEveryRowTakes(arm, written).equals(Optional.of(false))
                    ? Optional.of(new WhyNoValueTakesTheArm.ByWhatIsWritten(List.copyOf(written),
                            arm.caseTypes()))
                    : Optional.empty();
        }
        // An arm in a copy of one of the language's operations is no arm of the model.
        if (construct.isEmpty()) {
            return Optional.empty();
        }
        if (meanings == MeaningsOfABody.NONE) {
            return refusedByThePosition(arm);
        }
        return meanings.at(new MeaningsOfABody.Site(construct.get(),
                        new MeaningsOfABody.Part.OfACase(index)))
                .map(stated -> WhatTheRulesLeave.admits(stated, true, read))
                .flatMap(answer -> answer instanceof AWayThrough.RuledOut(var why)
                        ? Optional.of(new WhyNoValueTakesTheArm.ByWhatItStates(why))
                        : Optional.empty());
    }

    /** Every case {@code arm} is written for refused by the rules of the position the scrutinee
     *  stands at, where it stands at one: an arm goes only where all of them go. */
    private Optional<WhyNoValueTakesTheArm> refusedByThePosition(Core.Case arm) {
        if (arm.caseTypes().isEmpty()
                || !(reads.pathOf(match.scrutinee(), newtypes) instanceof PathResolution.At(
                        TermPath at))) {
            return Optional.empty();
        }
        Position position = read.domain().at(at);
        if (position == null) {
            return Optional.empty();
        }
        List<Refinement> reaches = new ArrayList<>();
        for (ResolvedCase each : arm.pattern().cases()) {
            reaches.addAll(Refinement.allOf(each));
        }
        return reaches.stream().allMatch(each -> position.admissionOf(each) instanceof Admits.Refused)
                ? Optional.of(new WhyNoValueTakesTheArm.ByTheRulesOfThePosition(at,
                        arm.caseTypes()))
                : Optional.empty();
    }
}
