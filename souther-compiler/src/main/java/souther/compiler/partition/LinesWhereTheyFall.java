package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PlacementFiling;
import souther.compiler.inputs.PlacementSeed;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.RuleAddress;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;

/**
 * The lines a model draws, each at the positions the name it was drawn on reaches.
 *
 * <p>A rule names a location in the words of the value it was written in, and a row writes a value
 * at a position. Where the two are the same place, nothing happens here. Where they are not — a
 * field every case of a sum spreads is readable on the sum and a row writes it under one case — one
 * line comes out as one line per case, on the same number and from the same rule.
 *
 * <p><b>Before anything is matched against an axis.</b> Past this, a line names a position, so what
 * divides a position is settled by the terms being the same term. Left to the matching, a line drawn
 * on a name no axis carries would be a line nothing divides — which reads as a comparison this
 * compiler could not take in, and is a cause nobody established.
 */
public final class LinesWhereTheyFall {

    /**
     * The lines, at the positions their names reach, and the ones this had nowhere to put.
     *
     * <p>A line that could not be placed is not among the first: passed on at the name it was
     * written at, it reaches the generator, which answers that it could not build a value there — a
     * place nobody meant and a reason nobody established. So it comes back as a finding naming the
     * rule, and a reader is told what actually happened to it.
     */
    public record Filed(List<Threshold> thresholds, List<GuardThresholds.Guards.Singled> singled,
                        List<LineDrawn> between, List<RuleWithoutALine> notPlaced) {

        public Filed {
            thresholds = List.copyOf(thresholds);
            singled = List.copyOf(singled);
            between = List.copyOf(between);
            notPlaced = List.copyOf(notPlaced);
        }
    }

    /** Every line at the positions its name reaches, and the ones this had nowhere to put. */
    public static Filed of(InputDomain inputs, List<Threshold> thresholds,
                           List<GuardThresholds.Guards.Singled> singled, List<LineDrawn> between,
                           souther.compiler.inputs.Quantities quantities, Symbols symbols) {
        List<Threshold> outThresholds = new ArrayList<>();
        List<GuardThresholds.Guards.Singled> outSingled = new ArrayList<>();
        List<LineDrawn> outBetween = new ArrayList<>();
        List<RuleWithoutALine> notPlaced = new ArrayList<>();
        for (Threshold each : thresholds) {
            for (NumericTerm term : termsOf(inputs, each.term(), symbols)) {
                outThresholds.add(new Threshold(term, each.parts(), each.valueBelongsBelow(),
                        each.origin()));
            }
        }
        for (GuardThresholds.Guards.Singled each : singled) {
            for (NumericTerm term : termsOf(inputs, each.term(), symbols)) {
                outSingled.add(new GuardThresholds.Guards.Singled(term, each.value(),
                        each.origin()));
            }
        }
        for (LineDrawn each : between) {
            place(inputs, each, quantities, symbols, outBetween, notPlaced);
        }
        return new Filed(outThresholds, outSingled, outBetween, notPlaced);
    }

    /**
     * One line between positions, at the positions the name it moves by reaches.
     *
     * <p>One name and no more. Where two of the names a line is drawn between reach positions under
     * the cases, which of those positions go together is a question about the model, and this is not
     * the reader that answers it.
     */
    private static void place(InputDomain inputs, LineDrawn line,
                              souther.compiler.inputs.Quantities quantities, Symbols symbols,
                              List<LineDrawn> out, List<RuleWithoutALine> notPlaced) {
        List<NumericTerm> crossing = new ArrayList<>();
        for (NumericTerm term : line.cuts().of().terms()) {
            if (termsOf(inputs, term, symbols).size() > 1) {
                crossing.add(term);
            }
        }
        if (crossing.size() > 1) {
            // Not passed on. A line at a name no row is written at reaches the generator, which
            // says it could not build a value there — a reason nobody established, about a place
            // nobody meant. What an author is owed is the pairing, and it is said here.
            notPlaced.add(new RuleWithoutALine(line.by().rule(), line.by().cited(),
                    new souther.compiler.inputs.FilingCoordinate.OfTerm(crossing.getFirst()),
                    new souther.compiler.inputs.BlockReason.CasePairingNotDetermined()));
            return;
        }
        if (crossing.isEmpty()) {
            out.add(line);
            return;
        }
        NumericTerm moves = crossing.getFirst();
        List<LineDrawn> made = new ArrayList<>();
        for (NumericTerm to : termsOf(inputs, moves, symbols)) {
            Cutting cut = line.cuts().movedTo(moves, to, inputs.ordersOf(to, symbols), quantities);
            if (cut != null) {
                made.add(new LineDrawn(cut, line.by()));
            }
        }
        // Nowhere to move it to and no reading said otherwise: the line stays as the model wrote it
        // rather than being dropped for having been about a name this could not place.
        out.addAll(made.isEmpty() ? List.of(line) : made);
    }

    /**
     * The term at each position the location it names reaches, which is the term itself wherever
     * that location is a position.
     *
     * <p>Left alone unless the reading has something to say. A term already at a position is at one,
     * and a term the reading of this input has no name for is one a caller here has no business
     * moving — what a rule of one value calls a place is that value's to say, and this is not the
     * reader that decides it.
     */
    private static List<NumericTerm> termsOf(InputDomain inputs, NumericTerm term,
                                             Symbols symbols) {
        TermPath path = term.path();
        if (inputs.at(path) != null) {
            return List.of(term);
        }
        // The value the comparison was written against, which is the parameter the location is
        // under. A location already naming a case is under no name of that value's, and comes back
        // with no address rather than with one this rewrote.
        RuleAddress address = RuleAddress.of(TermPath.of(path.head()), path);
        if (address == null) {
            return List.of(term);
        }
        PlacementFiling filing = inputs.file(PlacementSeed.of(TermPath.of(path.head()), term));
        List<NumericTerm> out = new ArrayList<>();
        for (PositionId at : filing.filedAt()) {
            Position position = inputs.at(at.at());
            // The same number of what stands there. A shared field is one field with one declared
            // type, so this holds; asked and answered all the same, because what may not arrive
            // further down is a term measured by an account written for another shape.
            NumericTerm moved = position == null ? null
                    : term.movedTo(at.at(), position.type(), symbols);
            if (moved != null) {
                out.add(moved);
            }
        }
        // Nothing to move it to, and the filing says why. The line stays as it was so that whoever
        // reads it reads the name the model wrote.
        return out.isEmpty() ? List.of(term) : List.copyOf(out);
    }


    private LinesWhereTheyFall() {}
}
