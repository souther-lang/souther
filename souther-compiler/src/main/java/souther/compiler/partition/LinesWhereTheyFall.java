package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.PlacementFiling;
import souther.compiler.inputs.PlacementSeed;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionId;
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
 * <p><b>What comes out, for each line.</b> Every term the line cuts is either left where the model
 * wrote it or filed at one or more positions. Where no term of the line was filed, the line stays
 * where it was written. Where one was, the line comes out once at each position that term was filed
 * at. Where more than one was, which of their positions go together is not settled here and the line
 * is not placed.
 *
 * <p><b>Before anything is matched against an axis.</b> What divides a position is settled by the
 * terms being the same term. Left to the matching, a line drawn on a name no axis carries would be a
 * line nothing divides — which reads as a comparison this compiler could not take in, and is a cause
 * nobody established.
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
            switch (standingOf(inputs, each.term(), symbols, each.origin())) {
                case WhereTheNameStands.AsWritten(NumericTerm at) ->
                        outThresholds.add(threshold(each, at));
                case WhereTheNameStands.FiledAt(NumericTerm first, List<NumericTerm> rest) -> {
                    outThresholds.add(threshold(each, first));
                    rest.forEach(at -> outThresholds.add(threshold(each, at)));
                }
            }
        }
        for (GuardThresholds.Guards.Singled each : singled) {
            switch (standingOf(inputs, each.term(), symbols, each.origin())) {
                case WhereTheNameStands.AsWritten(NumericTerm at) ->
                        outSingled.add(singled(each, at));
                case WhereTheNameStands.FiledAt(NumericTerm first, List<NumericTerm> rest) -> {
                    outSingled.add(singled(each, first));
                    rest.forEach(at -> outSingled.add(singled(each, at)));
                }
            }
        }
        for (LineDrawn each : between) {
            place(inputs, each, quantities, symbols, outBetween, notPlaced);
        }
        return new Filed(outThresholds, outSingled, outBetween, notPlaced);
    }

    /** The same threshold, measured at {@code at}. */
    private static Threshold threshold(Threshold each, NumericTerm at) {
        return new Threshold(at, each.parts(), each.valueBelongsBelow(), each.origin());
    }

    /** The same singled-out value, measured at {@code at}. */
    private static GuardThresholds.Guards.Singled singled(GuardThresholds.Guards.Singled each,
                                                          NumericTerm at) {
        return new GuardThresholds.Guards.Singled(at, each.value(), each.origin());
    }

    /**
     * One line, at the positions the name it moves by was filed at.
     *
     * <p>One name and no more. Where two of the names a line is drawn between were filed under the
     * cases, which of those positions go together is a question about the model, and this is not the
     * reader that answers it.
     *
     * <p>How many names were filed and how many positions one of them was filed at are separate
     * questions, and they are asked apart: the first decides whether there is a line to place, the
     * second how many come out of it. Answered off one count, a name filed at one position and a
     * name left where it was written would be the same answer.
     */
    private static void place(InputDomain inputs, LineDrawn line,
                              souther.compiler.inputs.Quantities quantities, Symbols symbols,
                              List<LineDrawn> out, List<RuleWithoutALine> notPlaced) {
        List<FiledName> filed = new ArrayList<>();
        for (NumericTerm term : line.cuts().of().terms()) {
            switch (standingOf(inputs, term, symbols, line.by())) {
                // Where the model wrote it, so the line is already about the position it names.
                case WhereTheNameStands.AsWritten _ -> { }
                case WhereTheNameStands.FiledAt at -> filed.add(new FiledName(term, at));
            }
        }
        if (filed.size() > 1) {
            // Not passed on. A line at a name no row is written at reaches the generator, which
            // says it could not build a value there — a reason nobody established, about a place
            // nobody meant. What an author is owed is the pairing, and it is said here.
            notPlaced.add(new RuleWithoutALine(line.by().rule(), line.by().cited(),
                    new souther.compiler.inputs.FilingCoordinate.OfTerm(filed.getFirst().name()),
                    new souther.compiler.inputs.BlockReason.CasePairingNotDetermined()));
            return;
        }
        if (filed.isEmpty()) {
            out.add(line);
            return;
        }
        FiledName moves = filed.getFirst();
        List<LineDrawn> made = new ArrayList<>();
        made.add(taken(line, moves.name(), moves.at().first(), inputs, quantities, symbols));
        for (NumericTerm to : moves.at().rest()) {
            made.add(taken(line, moves.name(), to, inputs, quantities, symbols));
        }
        out.addAll(made);
    }

    /**
     * The line, with the quantity it is drawn on taken at {@code to}.
     *
     * <p>What a quantity can be is settled by the orders its terms are on, and one name filed at
     * more than one position is filed at one field on one order. So the move holds at all of them or
     * at none, and a subset is this compiler contradicting itself rather than a line to place at
     * fewer places than the name was filed.
     */
    private static LineDrawn taken(LineDrawn line, NumericTerm moves, NumericTerm to,
                                   InputDomain inputs,
                                   souther.compiler.inputs.Quantities quantities, Symbols symbols) {
        Cutting cut = line.cuts().movedTo(moves, to, inputs.ordersOf(to, symbols), quantities);
        if (cut == null) {
            throw new IllegalStateException(
                    "`" + moves + "` was filed at " + to + " and the line on it cannot be taken "
                            + "there, though it is taken at every other position it was filed at");
        }
        return new LineDrawn(cut, line.by());
    }

    /** One of a line's names that was filed, and where. */
    private record FiledName(NumericTerm name, WhereTheNameStands.FiledAt at) {}

    /**
     * Whether the name this term is written at was filed anywhere, and at which positions.
     *
     * <p>Left alone unless the reading has something to say. A term already at a position is at one,
     * and a term the reading of this input has no name for is one a caller here has no business
     * moving — what a rule of one value calls a place is that value's to say, and this is not the
     * reader that decides it.
     *
     * <p>The one place a filing is read as a line placement. What each of the three outcomes does
     * about the line is written down here rather than worked out from how many of them were filings,
     * so a fourth outcome is a question asked of this method and not an answer it already gives.
     */
    private static WhereTheNameStands standingOf(InputDomain inputs, NumericTerm term,
                                                 Symbols symbols, OriginRef origin) {
        TermPath path = term.path();
        if (inputs.at(path) != null) {
            return new WhereTheNameStands.AsWritten(term);
        }
        // The value a rule naming this location is read of, which the reading answers. A location
        // already naming a case is under no name of that value's, and comes back with none rather
        // than with one this worked out for itself.
        InputDomain.RuleRoot root = inputs.rootNaming(path);
        if (root == null) {
            return new WhereTheNameStands.AsWritten(term);
        }
        PlacementFiling filing = inputs.file(
                PlacementSeed.of(root.at(), term, origin.rule(), origin.cited()));
        List<NumericTerm> filed = new ArrayList<>();
        for (souther.compiler.inputs.PlacementOutcome outcome : filing.outcomes()) {
            switch (outcome) {
                case souther.compiler.inputs.PlacementOutcome.Filed(PositionId at) ->
                        filed.add(taken(term, at, inputs, symbols));
                // The reading held to what it already said about this case: no row is written under
                // it, so there is no position there for a line to be about. Nothing is owed and
                // nothing is left over.
                case souther.compiler.inputs.PlacementOutcome.Refused _ -> { }
                // The reading stopped before it got there, and the position it stopped at says so.
                // The walk's depth is where a report stops being about one input rather than a
                // claim about the model, so the line is measured where the model wrote it.
                case souther.compiler.inputs.PlacementOutcome.Unresolved _ -> { }
            }
        }
        return filed.isEmpty() ? new WhereTheNameStands.AsWritten(term)
                : new WhereTheNameStands.FiledAt(filed.getFirst(),
                        filed.subList(1, filed.size()));
    }

    /**
     * The term as it is taken at the position it was filed at.
     *
     * <p>The same number of what stands there. A name filed at more than one position is filed at
     * one field, and one field has one declared type — so the operation and what it is taken of
     * agree everywhere or nowhere. Asked at each of them all the same, and a disagreement is this
     * compiler contradicting itself rather than a place to drop one.
     */
    private static NumericTerm taken(NumericTerm term, PositionId at, InputDomain inputs,
                                     Symbols symbols) {
        Position position = inputs.at(at.at());
        NumericTerm moved = position == null ? null
                : term.movedTo(at.at(), position.type(), symbols);
        if (moved == null) {
            throw new IllegalStateException(
                    "`" + term + "` was filed at " + at + " and cannot be taken there, though it is "
                            + "taken at every other position one name is filed at");
        }
        return moved;
    }

    /**
     * What became of one name a line or a threshold is written at.
     *
     * <p>Two, and which of the two it is says whether anything moves. Answered by a count of
     * positions, a name filed at one of them and a name nothing was filed for would be the same
     * answer — and the second must leave the line alone where the first must not.
     *
     * <p>How many positions a filing came to is a question inside {@link FiledAt} and not one of
     * these two, so a reader asking whether the name moved never reads it off a length.
     */
    private sealed interface WhereTheNameStands {

        /**
         * Nothing was filed for this name, so the line stays where the model wrote it.
         *
         * <p>Three ways to arrive and one answer to give: the term is already at a position of this
         * reading, this reading has no value whose rules name it, or the reading stopped before it
         * got there. They are unlike facts about the input and they are the same fact about the
         * line, which is the only question asked here.
         */
        record AsWritten(NumericTerm term) implements WhereTheNameStands {}

        /**
         * The name was filed, at these positions.
         *
         * <p>Held as one and the others so that being filed somewhere is what having one of these
         * means, rather than something a caller checks after building it. There is no way to write
         * a filing at no position.
         */
        record FiledAt(NumericTerm first, List<NumericTerm> rest) implements WhereTheNameStands {

            public FiledAt {
                rest = List.copyOf(rest);
            }
        }
    }

    private LinesWhereTheyFall() {}
}
