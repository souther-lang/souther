package souther.compiler.partition;

import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.PlacementFiling;
import souther.compiler.inputs.PlacementSeed;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.RulesWithNoLine;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;

/**
 * What a model measures, at the positions the name it is written at was filed — and where it was
 * written, where it was filed nowhere.
 *
 * <p>A rule names a location in the words of the value it was written in, and a row writes a value
 * at a position. Where the location is already the position, nothing happens here. Where it is not —
 * a field every case of a sum spreads is readable on the sum and a row writes it under one case —
 * one line comes out as one line per case, on the same number and from the same rule, wherever this
 * reading got as far as those positions — and wherever the quantity there runs as far as the line.
 * A case can hold its share of the field to less than the field allows, and a line the field reaches
 * is then one that case's quantity never does.
 *
 * <p><b>What comes out.</b> Every name a rule is written at is either left where the model wrote it
 * or filed at one or more positions. An end put on a number and a value singled out are about one
 * name, so they come out once at each position that name was filed at, and once as written where it
 * was filed nowhere. A line is about the names it is drawn between, so it takes one more question:
 * where none of them was filed the line stays where it was written, where one was it comes out once
 * at each position that one was filed at, and where more than one was, which of their positions go
 * together is not settled here and the line is not placed.
 *
 * <p>How many names were filed and how many positions one of them was filed at are separate
 * questions. Answered off one count, a name filed at one position and a name left where it was
 * written would be the same answer, and the second must leave the rule alone where the first must
 * not.
 *
 * <p><b>Before anything is matched against an axis.</b> What divides a position is settled by the
 * terms being the same term. Left to the matching, a line drawn on a name no axis carries would be a
 * line nothing divides — which reads as a comparison this compiler could not take in, and is a cause
 * nobody established.
 */
public final class LinesWhereTheyFall {

    /**
     * The measurements, each where the name it is written at was filed or left as written, and what
     * the positions this drew no line at are left with.
     *
     * <p>A line that could not be placed is not among the first: passed on at the name it was
     * written at, it reaches the generator, which answers that it could not build a value there — a
     * place nobody meant and a reason nobody established. So it comes back as a finding naming the
     * rule, and a reader is told what actually happened to it.
     *
     * <p>Nor is a line at a position whose quantity stops short of it. The name it was written at runs
     * as far as the line, or the reading would have said the rule draws nothing there; a position it
     * was filed at is held by a case's own rules to less, and it is said so at that position.
     */
    public record Filed(List<RuleEvidence> evidence, List<ClassingBlocker> blocked,
                        List<LineDrawn> between,
                        RulesWithNoLine noLine) {

        public Filed {
            evidence = List.copyOf(evidence);
            blocked = List.copyOf(blocked);
            between = List.copyOf(between);
        }

        /** The lines, for a reader that wants only those. Read off the one list and not kept
         *  beside it. */
        public List<Threshold> thresholds() {
            return RuleEvidence.linesIn(evidence);
        }

        /** The values singled out, likewise. */
        public List<GuardThresholds.Guards.Singled> singled() {
            return RuleEvidence.pointsIn(evidence);
        }
    }

    /**
     * Every measurement where its name was filed, and the lines this had nowhere to put.
     *
     * @param lines what the comparisons state about a position, each with the line it was read off
     * @param sets  what the rules state as sets of a position's values, which are read off no line
     */
    public static Filed of(InputReading read, List<LineEvidence> lines, List<RuleEvidence> sets,
                           List<ClassingBlocker> blocked, List<LineDrawn> between) {
        InputDomain inputs = read.domain();
        Symbols symbols = read.symbols();
        List<RuleEvidence> out = new ArrayList<>();
        List<LineDrawn> outBetween = new ArrayList<>();
        RulesWithNoLine.Gathered noLine = new RulesWithNoLine.Gathered();
        // One pass in the order the rules were read, so what comes out is in that order too. A pass
        // per kind of thing a rule can say puts every range before every equality, whatever order a
        // body wrote them in, and every reader downstream takes the numbers in that order.
        for (LineEvidence each : lines) {
            RuleEvidence stated = each.evidence();
            switch (standingOf(inputs, stated.at(), read.rules().inners(), symbols, stated.by())) {
                // Where the model wrote it, which is the quantity the comparison was read on. Whether
                // the line reaches it was asked there, and a line that does not never got this far.
                case WhereTheNameStands.AsWritten _ -> out.add(stated);
                // Every number the name stands at, filed together. Filing is one rule to as many
                // positions as its name reaches, so a piece put out one part at a time can leave the
                // others behind — and the account that runs after this begins with what comes out
                // of here, so it has nothing to say those others were ever expected. There is no
                // partial filing to write: what a name stands at is one list and this maps it.
                case WhereTheNameStands.FiledAt filed -> filed.all().forEach(to -> {
                    Cutting moved = lineAt(each.line(), stated.at(), to, read.quantities());
                    if (reaches(moved, each.by(), read.quantities())) {
                        out.add(measuredAt(stated, to));
                    } else {
                        outside(to, each.by(), noLine);
                    }
                });
            }
        }
        for (RuleEvidence each : sets) {
            // A set told from the rest is held to what a position takes where its classes are
            // composed ({@link Classing}), so there is nothing here to ask before it moves.
            standingOf(inputs, each.at(), read.rules().inners(), symbols, each.by()).all()
                    .forEach(at -> out.add(measuredAt(each, at)));
        }
        // And the rules that would have divided a position and did not, through the same authority
        // and in the same act. What a name reaches is one answer, and a blocker filed by anything
        // else would be at the position the rule was written about while the evidence beside it had
        // moved — so a position would be composed out of rules one of these was meant to stop.
        List<ClassingBlocker> outBlocked = new ArrayList<>();
        for (ClassingBlocker each : blocked) {
            standingOf(inputs, each.at(), read.rules().inners(), symbols, each.by()).all()
                    .forEach(at -> {
                NumericTerm.FromOnePosition here = at.atOnePosition();
                // Held to what the evidence beside it is held to. A destination no single position
                // answers is this compiler contradicting the reading that produced the blocker, and
                // dropped quietly it would take a position's denominator back to the rules that
                // worked — which is the whole of what a blocker is for.
                if (here == null) {
                    throw new IllegalStateException(
                            "`" + each.at() + "` is a distinction of a position and was filed at `"
                                    + at + "`, which no single position answers");
                }
                outBlocked.add(each.measuredAt(here));
            });
        }
        for (LineDrawn each : between) {
            place(read, each, outBetween, noLine);
        }
        return new Filed(out, outBlocked, outBetween, noLine.found());
    }

    /**
     * Whether the quantity a line was moved to runs as far as it — the question the reading asked
     * of the quantity the rule was written about, asked of this one.
     */
    private static boolean reaches(Cutting moved, LineOrigin by, Quantities quantities) {
        return moved.reachedIn(quantities.region(), Border.drawnByAnInvariant(by));
    }

    /**
     * What the position the line was moved to, and does not reach, is left with.
     *
     * <p>At that position and nowhere else. What failed is the filing of one name at one case, so
     * the other names of the line — a position it is drawn against, which the line reaches under
     * every other case — are told nothing: the rule draws its line there, at the cases that reach
     * it. In the words a quantity the line never reaches is left with
     * ({@link ComparisonAssessment.OutsideTheDomain#leaves}), since that is what this position is.
     *
     * <p>Nothing is passed on from here either. A piece of evidence passed on is one the stage after
     * this owes an answer about, and there is no border here for it to answer with.
     */
    private static void outside(NumericTerm at, LineOrigin by, RulesWithNoLine.Gathered noLine) {
        noLine.add(by.cited(), FilingCoordinate.of(at),
                ComparisonAssessment.OutsideTheDomain.leaves());
    }


    /**
     * The same piece of evidence, measured at {@code at}.
     *
     * <p>What a rule states is about one position's values, so the number it moved to answers one.
     * What a name is filed at is a field of a value and a term is taken at it the way it was taken
     * where it was written, so a move that left the number answered by no single place would be
     * this compiler contradicting the reading that produced the evidence.
     */
    private static RuleEvidence measuredAt(RuleEvidence evidence, NumericTerm at) {
        NumericTerm.FromOnePosition here = at.atOnePosition();
        if (here == null) {
            throw new IllegalStateException(
                    "`" + evidence.at() + "` is what a rule states about one position and was filed"
                            + " at `" + at + "`, which no single position answers");
        }
        return switch (evidence) {
            case RuleEvidence.Divides(Threshold line) ->
                    new RuleEvidence.Divides(thresholdAt(line, here));
            case RuleEvidence.Singles(GuardThresholds.Guards.Singled point) ->
                    new RuleEvidence.Singles(singledAt(point, here));
            // The values are the position's own, so moving the division moves where it is measured
            // and nothing else. What each side holds was worked out where the rule was read, and a
            // filing that worked them out again would be a second answer about one rule.
            case RuleEvidence.BySet(SetStatement division) ->
                    new RuleEvidence.BySet(new SetStatement(here, division.whenTrue(),
                            division.whenFalse(), division.statement(), division.origin()));
        };
    }

    /** The same threshold, measured at {@code at}. */
    private static Threshold thresholdAt(Threshold each, NumericTerm.FromOnePosition at) {
        return new Threshold(at, each.parts(), each.valueBelongs(), each.origin());
    }

    /** The same singled-out value, measured at {@code at}. */
    private static GuardThresholds.Guards.Singled singledAt(GuardThresholds.Guards.Singled each,
                                                            NumericTerm.FromOnePosition at) {
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
    private static void place(InputReading read, LineDrawn line,
                              List<LineDrawn> out, RulesWithNoLine.Gathered noLine) {
        InputDomain inputs = read.domain();
        Quantities quantities = read.quantities();
        Symbols symbols = read.symbols();
        List<FiledName> filed = new ArrayList<>();
        // What moves is a term of a form; a quantity that is no form has none to move, and its line
        // stays where it was read.
        List<NumericTerm> terms = line.cuts().of() instanceof LinearQuantity form
                ? form.terms() : List.of();
        for (NumericTerm term : terms) {
            switch (standingOf(inputs, term, read.rules().inners(), symbols, line.by())) {
                // Where the model wrote it, so the line is already about the position it names.
                case WhereTheNameStands.AsWritten _ -> { }
                case WhereTheNameStands.FiledAt at -> filed.add(new FiledName(term, at));
            }
        }
        if (filed.size() > 1) {
            // Not passed on. A line at a name no row is written at reaches the generator, which
            // says it could not build a value there — a reason nobody established, about a place
            // nobody meant. What an author is owed is the pairing, and it is said here.
            // The line is what has nowhere to go: the rule was read, an end came out of it, and
            // which of the positions it runs between is what nothing worked out.
            noLine.boundaryUndetermined(line.by().cited(),
                    new FilingCoordinate.OfTerm(filed.getFirst().name()),
                    new BlockReason.CasePairingNotDetermined());
            return;
        }
        if (filed.isEmpty()) {
            out.add(line);
            return;
        }
        FiledName moves = filed.getFirst();
        // At each position, and asked at each whether the quantity there reaches the line: a case's
        // own rules can stop it short of a line the name it was written at runs past.
        for (NumericTerm to : moves.at().all()) {
            Cutting moved = lineAt(line.cuts(), moves.name(), to, quantities);
            if (reaches(moved, line.by(), quantities)) {
                out.add(new LineDrawn(moved, line.by()));
            } else {
                outside(to, line.by(), noLine);
            }
        }
    }

    /**
     * The line, with the quantity it is drawn on taken at {@code to}.
     *
     * <p>What a quantity can be is settled by the orders its terms are on, and one name filed at
     * more than one position is filed at one field on one order. So the move holds at all of them or
     * at none, and a subset is this compiler contradicting itself rather than a line to place at
     * fewer places than the name was filed.
     */
    private static Cutting lineAt(Cutting line, NumericTerm moves, NumericTerm to,
                                  Quantities quantities) {
        Cutting cut = line.movedTo(moves, to, quantities);
        if (cut == null) {
            throw new IllegalStateException(
                    "`" + moves + "` was filed at " + to + " and the line on it cannot be taken "
                            + "there, though a name is filed at one field on one order");
        }
        return cut;
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
                                                 NewtypeInners inners, Symbols symbols,
                                                 RuleEvidenceOrigin origin) {
        TermPath path = term.subjectPath();
        if (inputs.at(path) != null) {
            return new WhereTheNameStands.AsWritten(term);
        }
        // The value a rule naming this location is read of, which the reading answers. A location
        // already naming a case is under no name of that value's, and comes back with none rather
        // than with one this worked out for itself.
        souther.compiler.inputs.RuleAddress address = inputs.rootNaming(path);
        if (address == null) {
            return underEachCase(inputs, term, inners, symbols);
        }
        PlacementFiling filing = inputs.file(
                PlacementSeed.of(address, term, origin.cited()));
        List<NumericTerm> filed = new ArrayList<>();
        for (souther.compiler.inputs.PlacementOutcome outcome : filing.outcomes()) {
            switch (outcome) {
                case souther.compiler.inputs.PlacementOutcome.Filed(PositionId at) ->
                        filed.add(termAt(term, at, inputs, inners, symbols));
                // The reading held to what it already said about this case: no row is written under
                // it, so there is no position there for a line to be about. Nothing is owed and
                // nothing is left over.
                case souther.compiler.inputs.PlacementOutcome.Refused _ -> { }
                // The reading stopped before it got there, and the position it stopped at says so.
                // Where the walk stopped is an answer about the walk and not about the model, so
                // the line is measured where the model wrote it — which is a position the reading
                // has, because a path the measurement names is one the reading was built over.
                case souther.compiler.inputs.PlacementOutcome.Unresolved _ -> { }
            }
        }
        return filed.isEmpty() ? new WhereTheNameStands.AsWritten(term)
                : new WhereTheNameStands.FiledAt(filed.getFirst(),
                        filed.subList(1, filed.size()));
    }

    /**
     * Where a term no rule of the parameter's value names stands, as the reading of the names the
     * cases of a sum spread answers it ({@link NameReach#standingOf}): the element of a container
     * that a name every case spreads holds is read under each case and stands under each, so it is
     * filed at each of them that the reading holds — and as written where no name crosses.
     */
    private static WhereTheNameStands underEachCase(InputDomain inputs, NumericTerm term,
                                                    NewtypeInners inners, Symbols symbols) {
        List<NameReach.CaseStanding> standings = switch (inputs.reach().standingOf(
                term.subjectPath())) {
            case NameReach.Standing.AtThePathItself _ -> List.of();
            case NameReach.Standing.UnderTheCases(var under) -> under;
            case NameReach.Standing.CasesIncomplete(var under, var _) -> under;
        };
        List<NumericTerm> filed = new ArrayList<>();
        for (NameReach.CaseStanding each : standings) {
            Position position = inputs.at(each.position());
            NumericTerm moved = position == null ? null
                    : term.movedTo(each.position(), position.type(), inners, symbols);
            if (moved != null) {
                filed.add(moved);
            }
        }
        return filed.isEmpty() ? new WhereTheNameStands.AsWritten(term)
                : new WhereTheNameStands.FiledAt(filed.getFirst(), filed.subList(1, filed.size()));
    }

    /**
     * The term as it is taken at the position it was filed at.
     *
     * <p>The same number of what stands there. A name filed at more than one position is filed at
     * one field, and one field has one declared type — so the operation and what it is taken of
     * agree everywhere or nowhere. Asked at each of them all the same, and a disagreement is this
     * compiler contradicting itself rather than a place to drop one.
     */
    private static NumericTerm termAt(NumericTerm term, PositionId at, InputDomain inputs,
                                      NewtypeInners inners, Symbols symbols) {
        Position position = inputs.at(at.at());
        NumericTerm moved = position == null ? null
                : term.movedTo(at.at(), position.type(), inners, symbols);
        if (moved == null) {
            throw new IllegalStateException(
                    "`" + term + "` was filed at " + at + " and cannot be taken there, though a "
                            + "name is filed at one field and one field has one declared type");
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
         * Every number the name stands at, never none.
         *
         * <p>Asked as the whole list so that filing a piece of evidence is one step. Taken apart by
         * the caller — the first here, the rest there — the walk has as many places to add as the
         * shape has parts, and a piece filed at three positions can leave two behind while the
         * account beside it, which starts after this stage, has no way of knowing there were three.
         */
        default List<NumericTerm> all() {
            return switch (this) {
                case AsWritten(NumericTerm term) -> List.of(term);
                case FiledAt(NumericTerm first, List<NumericTerm> rest) -> {
                    List<NumericTerm> every = new ArrayList<>();
                    every.add(first);
                    every.addAll(rest);
                    yield List.copyOf(every);
                }
            };
        }

        /**
         * Nothing was filed for this name, so the line stays where the model wrote it.
         *
         * <p>Three ways to arrive and one answer to give: the term is already at a position of this
         * reading, this reading has no value whose rules name it, or the reading stopped before it
         * got there. They are unlike facts about the input and they are the same fact about the
         * line, which is the only question asked here.
         */
        record AsWritten(NumericTerm term) implements WhereTheNameStands {

            public AsWritten {
                if (term == null) {
                    throw new IllegalArgumentException("a name left alone is left at a term");
                }
            }
        }

        /**
         * The name was filed, at these positions.
         *
         * <p>Held as one and the others so that being filed somewhere is what having one of these
         * means, rather than something a caller checks after building it. The one place that could
         * still be nothing is the first, which is why it is refused here: a shape that admits an
         * empty filing and a check nobody runs come to the same thing.
         */
        record FiledAt(NumericTerm first, List<NumericTerm> rest) implements WhereTheNameStands {

            public FiledAt {
                if (first == null) {
                    throw new IllegalArgumentException(
                            "a filing is at a position, and this one is at none");
                }
                rest = List.copyOf(rest);
            }
        }
    }

    private LinesWhereTheyFall() {}
}
