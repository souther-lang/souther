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
            for (NumericTerm term : termsOf(inputs, each.term(), symbols, each.origin()).terms()) {
                outThresholds.add(new Threshold(term, each.parts(), each.valueBelongsBelow(),
                        each.origin()));
            }
        }
        for (GuardThresholds.Guards.Singled each : singled) {
            for (NumericTerm term : termsOf(inputs, each.term(), symbols, each.origin()).terms()) {
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
        java.util.Map<NumericTerm, List<NumericTerm>> reaches = new java.util.LinkedHashMap<>();
        for (NumericTerm term : line.cuts().of().terms()) {
            Reached where = termsOf(inputs, term, symbols, line.by());
            if (where.crosses()) {
                crossing.add(term);
                reaches.put(term, where.terms());
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
        List<NumericTerm> targets = reaches.get(moves);
        List<LineDrawn> made = new ArrayList<>();
        for (NumericTerm to : targets) {
            Cutting cut = line.cuts().movedTo(moves, to, inputs.ordersOf(to, symbols), quantities);
            // What a quantity can be is settled by the orders its terms are on, and one name
            // standing at more than one position stands at one field on one order. So the move
            // holds at all of them or at none, and a subset is this compiler contradicting itself
            // rather than a line to place at fewer places than the name reaches.
            if (cut == null) {
                throw new IllegalStateException(
                        "`" + moves + "` stands at " + to + " and the line on it cannot be taken "
                                + "there, though the name reaches " + targets.size() + " positions");
            }
            made.add(new LineDrawn(cut, line.by()));
        }
        out.addAll(made);
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
    private static Reached termsOf(InputDomain inputs, NumericTerm term, Symbols symbols,
                                   OriginRef origin) {
        souther.compiler.check.RuleRef by = origin.rule();
        souther.compiler.check.RuleCitation cited = origin.cited();
        TermPath path = term.path();
        if (inputs.at(path) != null) {
            return new Reached(List.of(term));
        }
        // The value a rule naming this location is read of, which the reading answers. A location
        // already naming a case is under no name of that value's, and comes back with none rather
        // than with one this worked out for itself.
        InputDomain.RuleRoot root = inputs.rootNaming(path);
        if (root == null) {
            return new Reached(List.of(term));
        }
        PlacementFiling filing = inputs.file(PlacementSeed.of(root.at(), term, by, cited));
        List<NumericTerm> out = new ArrayList<>();
        for (PositionId at : filing.filedAt()) {
            Position position = inputs.at(at.at());
            // The same number of what stands there. A name that stands at more than one position
            // stands at one field, and one field has one declared type — so the operation and what
            // it is taken of agree everywhere or nowhere. Asked at each of them all the same, and a
            // disagreement is this compiler contradicting itself rather than a place to drop one.
            NumericTerm moved = position == null ? null
                    : term.movedTo(at.at(), position.type(), symbols);
            if (moved == null) {
                throw new IllegalStateException(
                        "`" + term + "` stands at " + at + " and cannot be taken there, though it "
                                + "is taken at the " + filing.filedAt().size() + " positions one "
                                + "name reaches");
            }
            out.add(moved);
        }
        // A location this reading stopped short of is a location all the same: the walk's depth is
        // where a report stops being about one input and not a claim about the model, and the
        // position it stopped at already says so. So the line is measured where it was written, and
        // the only other way a name reaches nowhere does not arrive here at all — it is refused
        // where it arises.
        return out.isEmpty() ? new Reached(List.of(term)) : new Reached(List.copyOf(out));
    }

    /**
     * Where a name reached, and whether the reading answered that it reached nowhere.
     *
     * <p>The two apart, because they are two answers. A name at a position of this reading is at
     * one and nothing was followed; a name the rules of no value here can write is one this has no
     * business moving; and a name that was followed and came to nothing is a line the model draws
     * that this build cannot hold against any row. A list of terms says the first two and the third
     * alike, which is how the third came to be handed on as though it were the first.
     */
    private record Reached(List<NumericTerm> terms) {

        Reached {
            terms = List.copyOf(terms);
        }

        boolean crosses() {
            return terms.size() > 1;
        }
    }


    private LinesWhereTheyFall() {}
}
