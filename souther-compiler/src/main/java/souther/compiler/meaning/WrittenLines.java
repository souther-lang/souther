package souther.compiler.meaning;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Which of the lines a comparison's author drew each relation the comparison states is a place of,
 * and how it stands to that line, read off how the statement was derived.
 *
 * <p>Off the derivation and not the proposition, because the proposition holds a relation once
 * however many ways reached it: {@code Int.max(x, y) <= g} called on {@code p} and {@code p} states
 * {@code p <= g} once, and it is a place of the line under each arm of the operation. So a relation
 * is a place of every line some step that made it was reached under, and of no line it was not.
 *
 * <p>A step makes a relation where its conclusion holds it and none of the steps it was concluded
 * from does. What it was reached under is the arms taken at the choices above it that the
 * comparison's definition writes ({@link WrittenChoice}); a choice in a value a caller handed in is
 * passed through and adds nothing, so the places a call put one line stay places of that line.
 *
 * <p>And whether the relation is the line, put on the input ({@link AuthoredPointMapping}). What
 * the comparison's own reading makes is: a value a caller handed in comes into it as what each of
 * its cases answers, and the line lands once per case. What a caller's choice was decided by is
 * not — the condition of an {@code if} handed in, how the arguments of an operation the caller
 * applied stand, a comparison the caller wrote — and turns the statement somewhere this reading
 * cannot tie to the line. Where every reading of the comparison itself on the way to the line came
 * out one way whatever the row, such a place is shown to be no place of the line at all.
 */
public final class WrittenLines {

    /**
     * Where a walk is: under which of the author's lines, where a row takes the arms of it, whether
     * it came through what decided a caller's choice, and whether it is inside another comparison
     * the author wrote — whose relation faces that comparison's sides and not this one's.
     */
    private record Under(WrittenLine line, Proposition taken, boolean decidedOutside,
                         boolean inAnother) {

        /** One arm further in, taken where {@code taking} holds as well. */
        Under then(WrittenLine.Arm arm, Proposition taking) {
            return new Under(line.then(arm), Proposition.all(List.of(taken, taking)),
                    decidedOutside, inAnother);
        }

        Under outside() {
            return new Under(line, taken, true, inAnother);
        }

        Under inAnotherComparison() {
            return new Under(line, taken, decidedOutside, true);
        }
    }

    /**
     * How one relation was seen under one line: made somewhere the comparison's definition wrote,
     * facing the comparison's own sides as {@code facing} says and made by the comparison's own
     * reading where {@code itsOwn}; or made past what decided a caller's choice, where
     * {@code facing} is null.
     */
    private record Seen(Derivation.AComparisonRead.Facing facing, boolean itsOwn) {

        boolean proven() {
            return facing != null;
        }
    }

    private final ExpansionLineage comparison;
    private final Conclusion concluded;
    private final Map<Derivation, Set<String>> made = new IdentityHashMap<>();
    /** What each step whose relations were gathered concludes. */
    private final Map<Derivation, Proposition> conclusions = new IdentityHashMap<>();
    private final Map<Derivation, Set<Under>> walked = new IdentityHashMap<>();
    private final Map<String, Map<WrittenLine, Seen>> seen = new LinkedHashMap<>();
    /** The lines some relation of the comparison's own was made under. */
    private final Set<WrittenLine> drawn = new HashSet<>();
    /** The lines under which the comparison's own reading came out one way whatever the row. */
    private final Set<WrittenLine> settled = new HashSet<>();
    /** Each relation made, held, under its spelling. */
    private final Map<String, Proposition.Compared> stated = new HashMap<>();
    /** Where a row takes the arms of each line some relation was made under. */
    private final Map<WrittenLine, Proposition> taken = new LinkedHashMap<>();

    private WrittenLines(ExpansionLineage comparison, Optional<ModelOccurrence> where) {
        this.comparison = comparison;
        this.concluded = new Conclusion(where);
    }

    /**
     * For each relation {@code how} concludes, spelled as {@link Proposition.Compared#heldKey}, the
     * lines of the comparison standing in {@code comparison} it is a place of, and how it stands to
     * each; and where a row takes the arms of each of those lines.
     *
     * @param where   the construct of the model the comparison is, as the derivation was
     *                concluded at
     * @param written what the comparison claims, as its author wrote it, which is what a line of it
     *                claims where no reading of the line says more: the comparison holds or fails
     *                across each of its lines as it holds or fails across itself. Nothing for what
     *                an application states, whose lines are each what its operation's law says of
     *                it, and claim what that says
     */
    public static AuthorsLines of(
            Derivation how, ExpansionLineage comparison, Optional<ModelOccurrence> where,
            Optional<ComparisonClaim> written) {
        WrittenLines lines = new WrittenLines(comparison, where);
        lines.walk(how, new Under(WrittenLine.THE_COMPARISON, new Proposition.Always(true), false,
                false));
        Map<String, Map<WrittenLine, AuthoredPointMapping>> out = new LinkedHashMap<>();
        lines.seen.forEach((relation, under) -> {
            Map<WrittenLine, AuthoredPointMapping> each = new LinkedHashMap<>();
            // What an application states has no claim written for it, and each of its lines
            // claims what its relation, held, does — which is how a statement of several draws it.
            ComparisonClaim claims = written.orElseGet(() -> claimOf(
                    new Proposition.Compared(lines.stated.get(relation).relation(), true)));
            under.forEach((line, seen) -> {
                each.put(line, seen.proven()
                        ? new AuthoredPointMapping.Proven(line, claims, seen.facing(),
                                seen.itsOwn())
                        : lines.settled.contains(line) && !lines.drawn.contains(line)
                                ? new AuthoredPointMapping.NotAnAuthoredBoundary(line, claims)
                                : new AuthoredPointMapping.Undetermined(line, claims));
            });
            out.put(relation, each);
        });
        return new AuthorsLines(out, lines.taken);
    }

    private void walk(Derivation step, Under under) {
        if (!walked.computeIfAbsent(step, _ -> new HashSet<>()).add(under)) {
            return;
        }
        switch (step) {
            case Derivation.AChoiceAt(var at, var choice) -> {
                madeHere(step, List.of(choice), under);
                Optional<WrittenChoice> written = WrittenChoice.of(at, comparison);
                if (written.isPresent()) {
                    armsOf(written.get(), choice, under);
                } else {
                    handedIn(choice, under);
                }
            }
            case Derivation.AComparisonAt(var at, var read) -> {
                madeHere(step, List.of(read), under);
                walk(read, WrittenChoice.of(at, comparison).isPresent()
                        ? under.inAnotherComparison() : under.outside());
            }
            case Derivation.Restated(var read) -> {
                madeHere(step, List.of(read), under);
                walk(read, under.inAnotherComparison());
            }
            default -> {
                if (step instanceof Derivation.ACutThatCutsNothing && !under.decidedOutside()) {
                    settled.add(under.line());
                }
                List<Derivation> from = premisesOf(step);
                madeHere(step, from, under);
                from.forEach(each -> walk(each, under));
            }
        }
    }

    /**
     * Each arm of {@code choice}, walked under its own arm of {@code at}: what an arm answers where
     * a row takes the arm, and what selects it wherever the choice is made.
     */
    private void armsOf(WrittenChoice at, Derivation choice, Under under) {
        madeHere(choice, premisesOf(choice), under);
        Proposition always = new Proposition.Always(true);
        switch (choice) {
            case Derivation.IfThenElse(var condition, var then, var otherwise) -> {
                Proposition holds = concluded.of(condition);
                walk(condition, under.then(new WrittenLine.Arm(at, 0, true), always));
                walk(then, under.then(new WrittenLine.Arm(at, 0, false), holds));
                walk(otherwise, under.then(new WrittenLine.Arm(at, 1, false), holds.denied()));
            }
            case Derivation.MatchArms(var arms) -> arms(at, arms, under);
            case Derivation.AnOperationsCases(var _, var cases) -> arms(at, cases, under);
            case Derivation.ASizeInCases(var _, var cases) -> arms(at, cases, under);
            case Derivation.ByALaw(var _, var _, var law) -> ofTheLaw(at, law, under);
            default -> throw new IllegalArgumentException("a choice is an if, a match, the cases"
                    + " of an operation or a size, or a law: " + choice);
        }
    }

    private void arms(WrittenChoice at, List<Derivation.MatchArms.Arm> arms, Under under) {
        Proposition always = new Proposition.Always(true);
        List<Proposition> before = new ArrayList<>();
        for (int i = 0; i < arms.size(); i++) {
            Proposition selects = concluded.of(arms.get(i).selects());
            walk(arms.get(i).selects(), under.then(new WrittenLine.Arm(at, i, true), always));
            walk(arms.get(i).states(), under.then(new WrittenLine.Arm(at, i, false),
                    Derivation.taken(before, selects)));
            before.add(selects);
        }
    }

    /**
     * A choice a caller handed in, walked under the line it stands on: what each arm answers is
     * the line again, and what selects an arm is the caller's.
     */
    private void handedIn(Derivation choice, Under under) {
        madeHere(choice, premisesOf(choice), under);
        switch (choice) {
            case Derivation.IfThenElse(var condition, var then, var otherwise) -> {
                walk(condition, under.outside());
                walk(then, under);
                walk(otherwise, under);
            }
            case Derivation.MatchArms(var arms) -> handedIn(arms, under);
            case Derivation.AnOperationsCases(var _, var cases) -> handedIn(cases, under);
            case Derivation.ASizeInCases(var _, var cases) -> handedIn(cases, under);
            case Derivation.ByALaw(var _, var _, var law) -> walk(law, under);
            default -> throw new IllegalArgumentException("a choice is an if, a match, the cases"
                    + " of an operation or a size, or a law: " + choice);
        }
    }

    private void handedIn(List<Derivation.MatchArms.Arm> arms, Under under) {
        for (Derivation.MatchArms.Arm arm : arms) {
            walk(arm.selects(), under.outside());
            walk(arm.states(), under);
        }
    }

    /**
     * What a law the author applied an operation under states, each way it joins walked under an
     * arm of its own, as far as what the law is read over — the operation's arguments, which are
     * walked as any derivation is.
     */
    private void ofTheLaw(WrittenChoice at, Derivation step, Under under) {
        if (!walked.computeIfAbsent(step, _ -> new HashSet<>()).add(under)) {
            return;
        }
        switch (step) {
            case Derivation.ALawJoins(var _, var parts) -> {
                madeHere(step, parts, under);
                for (int i = 0; i < parts.size(); i++) {
                    ofTheLaw(at, parts.get(i), under.then(new WrittenLine.Arm(at, i, false),
                            new Proposition.Always(true)));
                }
            }
            case Derivation.ALawJoinsWithoutWhatImpliesAnother(var _, var each) -> {
                madeHere(step, premisesOf(step), under);
                for (int i = 0; i < each.size(); i++) {
                    if (each.get(i) instanceof Derivation.ALawJoinsWithoutWhatImpliesAnother
                            .Disjunct.Read(var read)) {
                        ofTheLaw(at, read, under.then(new WrittenLine.Arm(at, i, false),
                                new Proposition.Always(true)));
                    }
                }
            }
            default -> {
                List<Derivation> from = premisesOf(step);
                madeHere(step, from, under);
                from.forEach(each -> walk(each, under));
            }
        }
    }

    /** Files the relations {@code step} makes, concluded from {@code from}, under {@code under}. */
    private void madeHere(Derivation step, List<Derivation> from, Under under) {
        Set<String> here = new LinkedHashSet<>(relationsOf(step));
        from.forEach(each -> here.removeAll(relationsOf(each)));
        if (here.isEmpty()) {
            return;
        }
        // Facing the comparison's own sides only where it is the relation the comparison's own
        // reading read off them. A comparison written inside it faces the sides it wrote itself,
        // and so does what a count of statements about values written out was written out as: the
        // reading faces the count, and the statements it counts are no side of the comparison's.
        // Nor are the statements counts held against nought come to, which some element of what
        // they count meeting them is: the reading's relation is its own only where it is what the
        // reading concludes, and not where the statements a count was read as come to one.
        Derivation.AComparisonRead.Facing facing = null;
        String own = null;
        if (step instanceof Derivation.AComparisonRead read && !under.inAnother()
                && conclusionOf(step) instanceof Proposition.Compared compared
                && compared.relation().equals(read.relation())) {
            facing = read.facing();
            own = compared.heldKey();
        }
        if (!under.decidedOutside()) {
            drawn.add(under.line());
        }
        // Reached by more than one way to it, a line's arms are taken where any of them is.
        taken.merge(under.line(), under.taken(), (one, other) -> Proposition.any(List.of(one,
                other)));
        for (String each : here) {
            boolean itsOwn = each.equals(own);
            Seen how = new Seen(under.decidedOutside() ? null
                    : itsOwn ? facing : Derivation.AComparisonRead.Facing.NOTHING_WRITTEN, itsOwn);
            seen.computeIfAbsent(each, _ -> new LinkedHashMap<>())
                    .merge(under.line(), how, WrittenLines::together);
        }
    }

    /** What {@code stated} claims of the number its relation's form is held against. */
    public static ComparisonClaim claimOf(Proposition.Compared stated) {
        Rel rel = switch (stated.relation()) {
            case Relation.Affine affine -> affine.proposition();
            case Relation.Ordered ordered -> ordered.proposition();
        };
        return ComparisonClaim.stating(stated.holds() ? rel : rel.denied());
    }

    /**
     * What two ways to one relation under one line come to: shown where either shows it, and facing
     * nothing written where the two say it faces the comparison's sides differently.
     */
    private static Seen together(Seen one, Seen other) {
        if (one.proven() && other.proven()) {
            return one.equals(other) ? one
                    : new Seen(Derivation.AComparisonRead.Facing.NOTHING_WRITTEN,
                            one.itsOwn() && other.itsOwn());
        }
        return one.proven() ? one : other;
    }

    private Set<String> relationsOf(Derivation step) {
        Set<String> known = made.get(step);
        if (known == null) {
            known = new LinkedHashSet<>();
            Proposition out = concluded.of(step);
            conclusions.put(step, out);
            gather(out, known);
            made.put(step, known);
        }
        return known;
    }

    /** What {@code step} concludes, concluded once with its relations. */
    private Proposition conclusionOf(Derivation step) {
        relationsOf(step);
        return conclusions.get(step);
    }

    private void gather(Proposition stated, Set<String> into) {
        switch (stated) {
            case Proposition.Compared compared -> {
                into.add(compared.heldKey());
                this.stated.putIfAbsent(compared.heldKey(), compared);
            }
            case Proposition.All all -> all.parts().forEach(each -> gather(each, into));
            case Proposition.Any any -> any.parts().forEach(each -> gather(each, into));
            case Proposition.WhereItAnswers where -> {
                gather(where.answers(), into);
                gather(where.states(), into);
            }
            case Proposition.Some some -> gather(some.ofTheElement(), into);
            case Proposition.OnAnApplication each -> each.each().forEach(one -> gather(one, into));
            // The relations its statements hold, each one way round whichever way a choice of
            // them holds it.
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(one -> gather(one, into));
            case Proposition.SomeReachable reachable -> {
                gather(reachable.atANode(), into);
                reachable.noneBelow().ifPresent(none -> gather(none, into));
            }
            case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.Carried _, Proposition.Unread _ -> { }
        }
    }

    /** The steps {@code step} is concluded from. */
    static List<Derivation> premisesOf(Derivation step) {
        return switch (step) {
            case Derivation.ThroughABinding(var value) -> List.of(value);
            case Derivation.OfWhatWasKept(var element, var kept) -> with(element, kept);
            case Derivation.ABehaviorsBody(var _, var body) -> List.of(body);
            case Derivation.ARecursionsBody(var _, var body) -> List.of(body);
            case Derivation.OnEachValueWrittenOut(var each) -> each;
            case Derivation.AChoiceAt(var _, var choice) -> List.of(choice);
            case Derivation.AComparisonAt(var _, var read) -> List.of(read);
            case Derivation.Restated(var read) -> List.of(read);
            case Derivation.WhereItAnswers(var answers, var read) -> List.of(answers, read);
            case Derivation.WhereItIsAnswered(var of) -> List.of(of);
            case Derivation.IfThenElse(var condition, var then, var otherwise) ->
                    List.of(condition, then, otherwise);
            case Derivation.MatchArms(var arms) -> ofTheArms(arms);
            case Derivation.AnArmTaken(var before, var selects) -> with(selects, before);
            case Derivation.ItWasBuilt(var clauses) -> clauses;
            case Derivation.ItDeparted(var clauses, var _) -> clauses;
            case Derivation.OneOfItsArms(var arms) -> ofTheArms(arms);
            case Derivation.AComparisonOfAChoice(var cases) -> List.of(cases);
            case Derivation.AnOperationsCases(var _, var cases) -> ofTheArms(cases);
            case Derivation.ASizeInCases(var _, var cases) -> ofTheArms(cases);
            case Derivation.HeldAgainstAWrittenTruth(var truth, var _) -> List.of(truth);
            case Derivation.UnderADenial(var part, var _) -> List.of(part);
            case Derivation.Joined(var _, var left, var right) -> List.of(left, right);
            case Derivation.AnEmptinessCheck(var holds, var _) -> List.of(holds);
            case Derivation.ByALaw(var _, var _, var arguments) -> List.of(arguments);
            case Derivation.ALawJoins(var _, var parts) -> parts;
            case Derivation.OnTheSideALawNames(var _, var observed) -> List.of(observed);
            case Derivation.ALawQuantifies(var _, var meeting) -> List.of(meeting);
            case Derivation.AnOrderOfItsArguments(var _, var _, var arguments) ->
                    List.of(arguments);
            case Derivation.OverElementsWrittenOut(var each, var _, var _) -> each;
            case Derivation.OnEachApplication(var each) -> each;
            case Derivation.SomeElementMeeting(var _, var element, var _, var holds, var _) ->
                    holds.map(something -> List.of(element, something))
                            .orElseGet(() -> List.of(element));
            case Derivation.SomeElementEqualToAKey some -> List.of(some.atLeastOne());
            case Derivation.AcrossAWalk(var seed, var walked, var keeps, var _) ->
                    List.of(seed, walked, keeps);
            case Derivation.ATreeSearched(var _, var _, var atANode, var below, var once,
                                          var _) -> {
                List<Derivation> out = new ArrayList<>();
                out.add(atANode);
                below.ifPresent(out::addAll);
                out.add(once);
                yield out;
            }
            case Derivation.AReachedNode(var _, var _, var _, var atANode, var _) ->
                    List.of(atANode);
            case Derivation.Supposing(var supposed, var _, var _) -> List.of(supposed);
            case Derivation.OfTheEntryUnderTheKey(var selection, var about) ->
                    List.of(selection, about);
            case Derivation.OfTheLastToHoldItsValue(var element, var _, var _) ->
                    List.of(element);
            case Derivation.SomePieceMeeting(var _, var _, var _, var string, var piece) ->
                    string.map(held -> List.of(held, piece)).orElseGet(() -> List.of(piece));
            case Derivation.SomePieceEqualling(var piece, var _) -> List.of(piece);
            case Derivation.EveryElementMeetsIt(var _, var element, var holds, var _) ->
                    List.of(element, holds);
            case Derivation.ALawJoinsWithoutWhatImpliesAnother(var _, var each) -> each.stream()
                    .<Derivation>mapMulti((one, into) -> {
                        if (one instanceof Derivation.ALawJoinsWithoutWhatImpliesAnother
                                .Disjunct.Read(var read)) {
                            into.accept(read);
                        }
                    }).toList();
            case Derivation.WhereAnOperationKeepsIt(var _, var _, var handed) -> List.of(handed);
            case Derivation.ALawSettles _, Derivation.TheSameValue _,
                 Derivation.ALawComparison _, Derivation.ASignItsBoundsSettle _,
                 Derivation.WrittenOut _, Derivation.NoRunTakesIt _,
                 Derivation.TheRunStopsHere _, Derivation.WhatAWalkCarried _, Derivation.Folded _,
                 Derivation.ATruthOfASubject _, Derivation.PresentInASubject _,
                 Derivation.UnderOneOfItsOwnKeys _,
                 Derivation.CasesOfASubject _, Derivation.CasesWrittenOut _,
                 Derivation.SizeAboveNought _, Derivation.ACharacterInAClass _,
                 Derivation.OfAnElementOfAnAnswer _, Derivation.AComparisonRead _,
                 Derivation.ATruthCompared _, Derivation.ACutThatCutsNothing _,
                 Derivation.Stopped _ -> List.of();
        };
    }

    private static List<Derivation> ofTheArms(List<Derivation.MatchArms.Arm> arms) {
        List<Derivation> out = new ArrayList<>();
        arms.forEach(arm -> {
            out.add(arm.selects());
            out.add(arm.states());
        });
        return out;
    }

    private static List<Derivation> with(Derivation first, List<Derivation> rest) {
        List<Derivation> out = new ArrayList<>();
        out.add(first);
        out.addAll(rest);
        return out;
    }
}
