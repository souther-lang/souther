package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Location;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Owed;
import souther.compiler.check.Required;
import souther.compiler.check.RuleAccounting;
import souther.compiler.check.RuleRef;
import souther.compiler.check.UnreadComparison;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.diag.Citation;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * The values a behavior's body compares its inputs against.
 *
 * <p>A model's own thresholds, read where they are written. "Pre-approval is needed at a hundred
 * thousand" is not in any type — it is the comparison the behavior makes — and it is the line the
 * rows have to be written on both sides of.
 *
 * <p><b>A comparison is read wherever in a condition it is written</b> (spec
 * §boundary-coordinates). Which position the model divides is not a question about the
 * shape of the condition around the comparison, and it was answered as though it were: in
 *
 * <pre>if kind == Domestic &amp;&amp; cost &lt;= 100000</pre>
 *
 * the line at a hundred thousand went unread, and the position came back as one the model divides
 * no way — two tokens from the comparison that divides it.
 *
 * <p>Whether a comparison ran is not something the arms answer. A condition stops as soon as it is
 * settled, so under {@code A && B} an overseas request takes the else arm without {@code cost} having
 * been compared — and so does a request whose cost was compared and found too high. Each comparison
 * carries the site its own value is recorded at, which is what a line is measured against. What the
 * shape of the condition does decide is which arm a row that reached the comparison can be in, and
 * that is a question about the classes either side of the line: it is carried as a {@link OriginRef
 * .GuardOrigin.Witness}.
 *
 * <p>Three readers are kept apart here and are easy to run together. Which comparisons exist is
 * {@link #comparisonsIn}; which positions a comparison names at all is {@link #mentioned}; which
 * number a line can be drawn on is {@link #termOf}. The last is the narrowest, and asking it the
 * first two questions is how a position a body compares became a position nothing compares.
 */
public final class GuardThresholds {

    /**
     * What one reading of a body says about the comparisons in it.
     *
     * <p>One walk, because the operator is known once. Which side of the line each arm takes is not
     * recoverable from a {@link Threshold} — {@code x <= c} and {@code x > c} both put {@code c} on
     * the low side and their {@code then} arms are opposite halves — so what a row reaching a
     * comparison can be in is carried as {@link OriginRef.GuardOrigin.Witness} where the operator
     * is still in hand, and which values arrive is asked of the reading of the whole body.
     */
    public record Guards(List<Threshold> thresholds,
                         List<UnreadRule> unread, List<Singled> singled,
                         List<Border> between,
                         List<AtAPosition> accounting) {

        public static final Guards NONE =
                new Guards(List.of(), List.of(), List.of(), List.of(), List.of());

        /**
         * One comparison's accounting, and the position a reader is sent to for it.
         *
         * <p>The position is beside the accounting rather than inside it. What a rule raises is
         * about a subject of its own — the number a line falls on — and where in a behavior's inputs
         * that number is read from is what a document keys the question by, which is a question
         * about the walk that found it.
         */
        public record AtAPosition(TermPath at, NumericTerm term, RuleAccounting accounting) {
            public AtAPosition {
                if (at == null || accounting == null) {
                    throw new IllegalArgumentException("an accounting is filed somewhere");
                }
            }
        }

        /**
         * A value a body singles out rather than orders.
         *
         * <p>Apart from a {@link Threshold}, which says where one range ends and the next begins. An
         * equality says nothing about ranges: what it distinguishes is the value from every other
         * value, and reading it as a place to cut would put a distinction between the two sides into
         * a partition the model never drew.
         */
        public record Singled(NumericTerm term, Place value, OriginRef origin) {}

        public Guards {
            thresholds = List.copyOf(thresholds);
            unread = List.copyOf(unread);
            accounting = List.copyOf(accounting);
            singled = List.copyOf(singled);
            between = List.copyOf(between);
        }
    }

    /** The thresholds one behavior's body compares its parameters against, and both arms of each
     * comparison. {@code plan} supplies the guard each one belongs to, so a boundary can later ask
     * whether the comparison ran and an arm can be found by the probe that counts it. */
    public static Guards of(String behavior, Core body, CoverageSites.Plan plan,
                            InputDomain inputs, Symbols symbols) {
        List<Threshold> found = new ArrayList<>();
        List<UnreadRule> unread = new ArrayList<>();
        List<Guards.AtAPosition> accounting = new ArrayList<>();
        List<Guards.Singled> singled = new ArrayList<>();
        List<Border> between = new ArrayList<>();
        walk(behavior, body, plan, InputReads.of(inputs), symbols, found, unread,
                singled, between, accounting);
        return new Guards(found, unread, singled, between, accounting);
    }

    private static void walk(String behavior, Core e, CoverageSites.Plan plan,
                             InputReads reads, Symbols symbols, List<Threshold> out,
                             List<UnreadRule> unread,
                             List<Guards.Singled> singled, List<Border> between,
                             List<Guards.AtAPosition> accounting) {
        if (e instanceof Core.If iff) {
            List<Core> read =
                    read(behavior, iff, plan, reads, symbols, out, singled, between, accounting);
            // Every comparison this condition holds that nothing turned into a line — asked of the
            // comparisons and not of the positions. One position carries more than one statement,
            // and a line read at it says nothing about the rest: kept per position, a threshold on
            // `x` swallowed the comparison beside it that nothing could read, which is "a result
            // exists, so the reading is complete".
            for (UnreadRule compared : comparedIn(behavior, iff, read, reads, symbols)) {
                if (unread.stream().noneMatch(had -> had.sameAs(compared))) {
                    unread.add(compared);
                }
            }
        }
        // A match case's body and an attempted construction's departure are expression slots, so the
        // generic walk reaches them; only the arms themselves are not children, and this walk does not
        // number arms.
        // Inside what a `let` binds, since that is where a name standing for an argument is read
        // as the argument: an expanded helper binds the call's argument to its own parameter, and a
        // walk that did not follow the binding would find its comparisons about nothing.
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        Core.forEachChild(e, child -> walk(behavior, child, plan, inside, symbols, out,
                unread, singled, between, accounting));
    }

    /**
     * Every position a condition compares, however the condition is written.
     *
     * <p>Names them and no more. Whether a line can be drawn on one is {@link #termOf}'s narrower
     * question, and this establishes only that the model draws something at this position — which is
     * exactly what {@code not derivable} would otherwise deny.
     */
    private static List<UnreadRule> comparedIn(String behavior, Core.If iff, List<Core> read,
                                               InputReads reads, Symbols symbols) {
        List<UnreadRule> out = new ArrayList<>();
        compared(behavior, iff, iff.cond(), read, reads, symbols, out);
        return out;
    }

    private static void compared(String behavior, Core.If iff, Core e, List<Core> read,
                                 InputReads reads, Symbols symbols, List<UnreadRule> out) {
        // By the comparison it is, and not by what it was about: two comparisons at one position are
        // two statements, and this one having been read is no answer about the other.
        if (e instanceof Core.Binary comparison && orders(comparison.op())
                && read.stream().anyMatch(each -> each == comparison)) {
            return;
        }
        if (e instanceof Core.Binary binary && orders(binary.op()) && writtenHere(binary)) {
            List<TermPath> named = new ArrayList<>();
            mentioned(binary.left(), reads, symbols, named);
            mentioned(binary.right(), reads, symbols, named);
            BlockReason.AboutARule why = why(binary, reads, symbols);
            // The rule the author wrote, read off the source. Which comparison it is is the
            // behavior and the construct; where a reader is sent is the fork it stands in and the
            // place it is written. Neither comes from the plan: a condition both of whose arms can
            // record nothing is numbered nowhere, and a model states its rules regardless.
            RuleRef.Guard rule = new RuleRef.Guard(behavior, binary.origin());
            souther.compiler.check.RuleCitation cited = citationOf(iff, binary);
            for (TermPath each : named) {
                // One per position the comparison names, and told from its neighbours by the rule
                // as well as the place. Kept by position alone, the second comparison of one
                // condition about one position was dropped as a repeat of the first — which is the
                // defect this finding is about, one level in.
                UnreadRule said = new UnreadRule(rule, cited, each, why);
                if (out.stream().noneMatch(had -> had.sameAs(said))) {
                    out.add(said);
                }
            }
        }
        // Inside what a `let` binds, wherever one is met. A helper expanded into a condition binds
        // the call's arguments there — inside the condition, not above the `if` — so a walk that
        // extended its scope only on the way down the body would read every comparison in an
        // expansion as being about nothing.
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        Core.forEachChild(e, child -> {
            // Not into a fork of its own. A condition can hold one — `guard (if a < b then ...)` —
            // and its comparisons are written in that fork rather than in this one, so citing them
            // here would take the word from one construct and the place from another. The walk that
            // found this fork reaches that one too, and reads it against itself.
            if (!(child instanceof Core.If)) {
                compared(behavior, iff, child, read, inside, symbols, out);
            }
        });
    }

    /**
     * Whether this comparison is written in code this compile can send a reader to.
     *
     * <p>A call is spliced into the body that makes it, so a comparison written in something else
     * stands in this tree. Where that something else is out of sight — a library this compile has
     * no file for — the comparison is not a rule anybody reading this behavior can act on:
     * {@code Int.clamp(0, 100, n) > 70} is one comparison an author wrote and two they cannot open,
     * and naming the second two tells them to edit a function they do not have.
     *
     * <p>A helper of their own is not one of these. It has a file, the report cites it where it is
     * written, and it is theirs to rewrite — so the line is drawn at what a reader can reach and
     * not at whether an expansion happened.
     *
     * <p>{@link Citation} and not the position, which cannot say this: a spliced node carries the
     * coordinates of the code it was copied from. {@link Citation.Elsewhere} is exactly "written
     * where this compile has no file", and it is the same answer
     * {@link souther.compiler.check.RuleCitation} renders.
     *
     * <p>Asked of the comparison and not of the fork above it. The one the author wrote sits
     * outside an expansion whose insides they did not, so a subtree is the wrong unit — and the
     * walk still goes through the expansion, because that is where a call's argument is bound and
     * a comparison read without it is about nothing.
     */
    private static boolean writtenHere(Core.Binary comparison) {
        return !(Citation.of(comparison.pos()) instanceof Citation.Elsewhere);
    }

    /**
     * Every position an expression names, however it is written.
     *
     * <p>Weaker than {@link #termOf} on purpose, and asked instead of it. That one answers whether a
     * line can be drawn — it wants a number the terms name — and this one answers whether the model
     * says anything about a position at all. Sharing a reader between the two turns an expression
     * the derivation does not model into a position nothing compares: {@code p.x + 1 < 10} named no
     * position, and came back as one the model divides no way two tokens from a comparison about it.
     */
    private static void mentioned(Core e, InputReads reads, Symbols symbols,
                                  List<TermPath> out) {
        if (!(e instanceof Core.PreservedCall)) {
            TermPath here = reads.pathOf(e, symbols);
            if (here != null) {
                if (!out.contains(here)) {
                    out.add(here);
                }
                return;   // what is under it is the same position, named once
            }
        }
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        Core.forEachChild(e, child -> mentioned(child, inside, symbols, out));
    }

    /**
     * What would have to change before this comparison could be a line.
     *
     * <p>{@link UnreadComparison}'s, which is where the answer is so that an invariant's clause of
     * the same shape gets the same one. What is this reader's own is how a position is looked up:
     * a body's read of a parameter is what names one here, and a coordinate of a value is what
     * names one over there.
     */
    static BlockReason.AboutARule why(Core.Binary comparison, InputReads reads,
                           Symbols symbols) {
        return UnreadComparison.why(sideOf(comparison.left(), reads, symbols),
                sideOf(comparison.right(), reads, symbols),
                quantityOf(comparison, reads, symbols));
    }

    /**
     * The positions the quantity this comparison cuts is over, or null where the arithmetic read no
     * form at all.
     *
     * <p>This reader's own, because the atoms are: a body names a position by what it reads of a
     * parameter. What is done with the answer is {@link UnreadComparison}'s, so a clause of the same
     * shape two declarations away is described in the same words.
     */
    private static java.util.Set<TermPath> quantityOf(Core.Binary comparison, InputReads reads,
                                                      Symbols symbols) {
        AffineReading read = AffineReading.of(comparison, reads, symbols);
        if (read == null) {
            return null;
        }
        java.util.Set<TermPath> over = new java.util.LinkedHashSet<>();
        for (NumericTerm atom : read.form().coefs().keySet()) {
            over.add(atom.path());
        }
        return over;
    }

    /**
     * What one side of a comparison came to here.
     *
     * <p>Which positions it names is {@link #mentioned}'s recursive question and which number a
     * line could be drawn on is {@link #termOf}'s narrower one, and the two are what tell a
     * position inside an expression from a position. Asked the narrow question alone,
     * {@code y + 1} named nothing and a comparison of two positions came back as a form nobody
     * could read.
     *
     * <p>The positions come from the one walk either way. Read again off the term where there is
     * one, a side would be carrying two answers to "which position is this about" and the
     * comparison between them would be settled by whichever the caller looked at.
     */
    private static UnreadComparison.Side<TermPath> sideOf(Core e, InputReads reads,
                                                          Symbols symbols) {
        List<TermPath> named = mentionedIn(e, reads, symbols);
        if (named.isEmpty()) {
            return new UnreadComparison.Side.NamesNothing<>();
        }
        return termOf(e, reads, symbols) == null
                ? new UnreadComparison.Side.NamesInside<>(new java.util.LinkedHashSet<>(named))
                : new UnreadComparison.Side.IsOne<>(named.getFirst(),
                        orderable(e.type(), symbols));
    }

    static List<TermPath> mentionedIn(Core e, InputReads reads, Symbols symbols) {
        List<TermPath> out = new ArrayList<>();
        mentioned(e, reads, symbols, out);
        return out;
    }

    /** Whether an operator is one that compares two values rather than combining two conditions. */
    static boolean orders(Hir.BinOp op) {
        return ComparisonClaim.places(op);
    }

    /**
     * The positions a line was drawn on here.
     *
     * <p>One condition can hold several. {@code A && B} is two comparisons and two lines, and which
     * arm stands as evidence for each is not the same answer — so each is read with the witness its
     * place in the condition leaves it, and the arms are numbered once for the {@code if} they both
     * belong to.
     */
    private static List<Core> read(String behavior, Core.If iff, CoverageSites.Plan plan,
                                   InputReads reads, Symbols symbols,
                                   List<Threshold> out,
                                   List<Guards.Singled> singled, List<Border> between,
                                   List<Guards.AtAPosition> accounting) {
        // The comparisons a line came of, and not the positions they were about. A position carries
        // more than one statement and reading one of them settles nothing about the others.
        List<Core> made = new ArrayList<>();
        // What a row leaves behind at these comparisons, taken before any of them is read. Which
        // shape of line a comparison draws is a later question and not one this depends on — read
        // after a constant had been found, the site was a thing only a line against a constant could
        // have, and a comparison of two positions had no way to say what had reached it.
        CoverageSites.GuardRef guard = guardOf(plan, iff);
        if (guard == null) {
            return made;   // no site for this `if`: nothing could answer for it
        }
        for (Placed each : comparisonsIn(iff.cond())) {
            // The plan numbered every comparison of an instrumented condition before anything read a
            // line off one, so this is here. Required rather than looked up leniently: a line whose
            // comparison has no site is this reader and the plan disagreeing about what a condition
            // is made of.
            int site = plan.requireComparisonSiteOf(each.comparison());
            // What the comparison cuts is one question with one answer ({@link Cutting}). What is
            // added here is what meeting the line takes, which is a guard's own answer and no other
            // rule's.
            Cutting cutting = Cutting.of(behavior, each.comparison(), reads, symbols);
            if (cutting == null) {
                raisesNoLine(accounting, behavior, iff, each.comparison(), reads, symbols);
                continue;
            }
            OriginRef.GuardOrigin origin = new OriginRef.GuardOrigin(
                    new RuleRef.Guard(behavior, each.comparison().origin()),
                    new OriginRef.GuardOrigin.Read(guard, site, Citation.of(iff.pos())),
                    cutting.valueBelongsBelow(), each.witness(), cutting.holdsAtTheValue(),
                    cutting.singles());
            NumericTerm divided = cutting.dividedPosition();
            if (divided == null) {
                // A line on something that is not one position's own values. Not added to `made`:
                // what the partition could not read here it still could not read, and a boundary
                // answering does not answer for it (spec §example-partition).
                // Null where the quantity does not reach the line, which is the line and not one of
                // its points: three times a length is never negative, and a rule comparing one
                // against a negative draws nothing.
                Border drawn = Border.at(cutting.target(), origin, cutting.within());
                if (drawn == null) {
                    raisesNoLine(accounting, behavior, iff, each.comparison(), reads,
                            symbols);
                    continue;
                }
                if (between.stream().noneMatch(had -> had.equals(drawn))) {
                    between.add(drawn);
                }
                List<TermPath> named = new ArrayList<>();
                mentioned(each.comparison().left(), reads, symbols, named);
                mentioned(each.comparison().right(), reads, symbols, named);
                if (named.isEmpty()) {
                    continue;   // a comparison about no position of the input raises nothing
                }
                // Filed at the position the reading names first, which is the one a line between two
                // would be read `on`. One comparison is one line however many positions it mentions.
                raises(accounting, behavior, iff, each.comparison(), named.get(0),
                        comparedTerm(each.comparison(), reads, symbols),
                        subjectsOf(each.comparison(), reads, symbols, null),
                        new Required.LineRead.ALineBetweenTwoPositions());
                continue;
            }
            made.add(each.comparison());
            // The value the classes meet at, which the reading of the comparison already
            // answered. Taken off the level the rule was written with, a rule that wrote a
            // multiple of the position named a class at a number the position never holds.
            Place value = cutting.dividedValue();
            if (cutting.singles()) {
                singled.add(new Guards.Singled(divided, value, origin));
            } else {
                out.add(new Threshold(divided, value, cutting.valueBelongsBelow(), origin));
            }
            raises(accounting, behavior, iff, each.comparison(), divided.path(), divided,
                    subjectsOf(each.comparison(), reads, symbols, null),
                    new Required.LineRead.ALineOnThePosition());
        }
        return made;
    }

    /** What a comparison nothing read raises, filed at the position the reading names first. */
    private static void raisesNoLine(List<Guards.AtAPosition> accounting, String behavior,
                                     Core.If iff, Core.Binary comparison, InputReads reads,
                                     Symbols symbols) {
        List<TermPath> named = new ArrayList<>();
        mentioned(comparison.left(), reads, symbols, named);
        mentioned(comparison.right(), reads, symbols, named);
        if (named.isEmpty()) {
            return;   // a comparison about no position of the input raises nothing about one
        }
        raises(accounting, behavior, iff, comparison, named.get(0),
                comparedTerm(comparison, reads, symbols),
                subjectsOf(comparison, reads, symbols, null),
                new Required.LineRead.NoLine(why(comparison, reads, symbols)));
    }

    /**
     * What the question is about, relative to the position it is filed at.
     *
     * <p>An invariant's subject is relative to the value its clause is on, and this is the same
     * thing one frame out. Which of the two it is was settled by the reading that found the term: a
     * {@code String} bounded on its length raises about the string and draws its line on the count,
     * and a document promises both spellings.
     */
    static Owed.Subject.OfAPosition subjectOf(NumericTerm term) {
        // A term that is a count says the line is on the count; anything else — a term over the
        // position's own value, or no term at all — leaves it on the position.
        return new Owed.Subject.OfAPosition("", term instanceof NumericTerm.SizeOf);
    }

    /**
     * Whether the comparison is about one of the behavior's positions or about two.
     *
     * <p>Off the source, by the walk that names positions however they are written. The operator
     * says what a comparison places and this says what it places it about, and neither is the
     * other's: {@code x == 10} singles a value out and {@code x == y} is a rule about a pair, under
     * one operator.
     */
    static Required.ComparisonSubject subjectsOf(Core.Binary comparison, InputReads reads,
                                                 Symbols symbols, BindingId answer) {
        boolean left = movesWithTheRow(comparison.left(), reads, symbols, answer);
        boolean right = movesWithTheRow(comparison.right(), reads, symbols, answer);
        if (left == right) {
            // Both, which is a rule about a pair; or neither, which says nothing about an input.
            // The place a relation's line falls is between the two sides, spelled as they are
            // written — a reader meets them beside each other on the row owed there.
            return left ? new Required.ComparisonSubject.Relation(
                    new Owed.Subject.OfComparison(Citation.of(comparison.pos())))
                    : new Required.ComparisonSubject.NoInput();
        }
        Core side = left ? comparison.left() : comparison.right();
        NumericTerm term = termOf(side, reads, symbols);
        if (term == null) {
            // It moves with the row and is not a number this reads — the answer, or an input read a
            // way the terms do not name. Nothing about an input's own values follows.
            return new Required.ComparisonSubject.NoInput();
        }
        return new Required.ComparisonSubject.AnInput(subjectOf(term), Owed.Subject.at(""));
    }

    /**
     * Whether what {@code e} comes to is chosen by the row.
     *
     * <p>An input's position is, and so is the answer a clause of an {@code ensures} names — what a
     * row chooses is what the behavior is applied to, and the answer follows from it. Everything
     * else is the same for every row, which is what makes the other side of a comparison a place
     * rather than a second moving thing.
     */
    private static boolean movesWithTheRow(Core e, InputReads reads, Symbols symbols,
                                           BindingId answer) {
        if (!mentionedIn(e, reads, symbols).isEmpty()) {
            return true;
        }
        return answer != null && reads(e, answer);
    }

    /** Whether anything in {@code e} reads the binding a rule calls the answer. */
    private static boolean reads(Core e, BindingId answer) {
        if (e instanceof Core.Read read && answer.equals(read.binding())) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] |= reads(child, answer));
        return found[0];
    }

    /** The number a comparison is about, from whichever side names one. */
    static NumericTerm comparedTerm(Core.Binary comparison, InputReads reads, Symbols symbols) {
        NumericTerm left = termOf(comparison.left(), reads, symbols);
        return left != null ? left : termOf(comparison.right(), reads, symbols);
    }

    /**
     * What one comparison raises, and what the reading of it answered.
     *
     * <p>Off the comparison and not off the lines that came back. A comparison states where the
     * values stop by being written that way, and a line this could not read is exactly the case
     * where nothing answers it — walked from the lines, such a rule would be one the model never
     * wrote.
     */
    private static void raises(List<Guards.AtAPosition> out, String behavior, Core.If iff,
                               Core.Binary comparison, TermPath at, NumericTerm term,
                               Required.ComparisonSubject of, Required.LineRead read) {
        out.add(new Guards.AtAPosition(at, term, RuleAccounting.ofComparison(
                new RuleRef.Guard(behavior, comparison.origin()),
                souther.compiler.check.ComparisonClaim.of(comparison.op()), of, read,
                // A comparison is written rather than named, so a reader is sent where the author
                // wrote it — the comparison's own place and not the fork's. Two comparisons of one
                // condition are two rules, and cited at the `if` they were one handle twice.
                //
                // The construct is the fork's, which is what a rule with no name is found by: an
                // `if` and a `guard` are two things an author wrote and a reader looks for two
                // different words. Asked of the comparison's own origin instead, the answer is
                // `BINARY`, which is not a construct a rule is written in at all.
                citationOf(iff, comparison))));
    }

    /**
     * How a reader finds a comparison, which is what construct it stands in and where it is
     * written.
     *
     * <p>Two coordinates from two places, and neither stands for the other. The fork says what to
     * call the thing the author wrote; the comparison says where in the file to look. A condition
     * holding two comparisons is two rules under one construct, so citing both at the fork would be
     * one handle twice.
     */
    static souther.compiler.check.RuleCitation.WrittenAt citationOf(Core.If iff,
                                                                   Core.Binary comparison) {
        return new souther.compiler.check.RuleCitation.WrittenAt(
                iff.origin().kind(), Citation.of(comparison.pos()));
    }

    /** One comparison of a condition, and which arms of the {@code if} prove it was evaluated. */
    private record Placed(Core.Binary comparison, OriginRef.GuardOrigin.Witness witness) {}

    /**
     * The comparisons a condition is made of, each with what its own place leaves as evidence.
     *
     * <p>Asked per comparison and not per condition. A condition that is nothing but {@code &&}
     * settles it for every operand at once, and so does one that is nothing but {@code ||}; a
     * condition made of both does not. In {@code A && (B || C)} the arm where the whole thing held
     * proves {@code A} was true and so proves {@code B} ran, while {@code C} ran only where
     * {@code B} was false — which is a difference between two operands of one condition, and a
     * single verdict over the whole cannot hold it.
     *
     * <p>Two facts are carried down, and they are not the same one. Whether this subtree is
     * evaluated at all on a given arm, and whether reaching that arm forces the subtree's own value
     * — because it is the second that says whether the operand to its left was true, which is what
     * decides whether the operand to its right ran.
     */
    private static List<Placed> comparisonsIn(Core condition) {
        List<Placed> out = new ArrayList<>();
        // At the top there is nothing above to have stopped the condition, and the arm taken is the
        // condition's own value.
        placed(condition, new Reached(true, true, true, true), out);
        return out;
    }

    /**
     * What reaching each arm of the enclosing {@code if} says about one subtree of its condition.
     *
     * <p>Four answers and not six, on a premise worth stating rather than leaving to be rediscovered.
     * A subtree can be forced true only where the whole condition is true and forced false only where
     * it is false — {@code &&} passes a true value down to both operands, {@code ||} passes a false
     * one, and neither passes anything the other way. So "false on {@code then}" and "true on
     * {@code else}" are unreachable and are not carried.
     *
     * <p>What makes that hold is that a condition is built from {@code &&} and {@code ||} and
     * nothing else. There is no negation operator: {@code Bool.not} is a helper, inlined to an
     * {@code if} whose condition is the comparison itself, so it never stands between a comparison
     * and the arms this is about. An operator that inverted a value inside a condition would break
     * the premise and want the other two answers, and would find this comment rather than a wrong
     * result.
     *
     * @param onThen    whether reaching the {@code then} arm implies this subtree was evaluated
     * @param onElse    the same for {@code else}
     * @param trueThen  whether reaching {@code then} implies this subtree's own value was true
     * @param falseElse whether reaching {@code else} implies its own value was false
     */
    private record Reached(boolean onThen, boolean onElse, boolean trueThen, boolean falseElse) {

        OriginRef.GuardOrigin.Witness witness() {
            if (onThen && onElse) {
                return OriginRef.GuardOrigin.Witness.BOTH;
            }
            if (onThen) {
                return OriginRef.GuardOrigin.Witness.THEN;
            }
            return onElse ? OriginRef.GuardOrigin.Witness.ELSE
                    : OriginRef.GuardOrigin.Witness.NEITHER;
        }
    }

    private static boolean combines(Hir.BinOp op) {
        return op == Hir.BinOp.AND || op == Hir.BinOp.OR;
    }

    private static void placed(Core e, Reached reached, List<Placed> out) {
        if (e instanceof Core.Binary binary && combines(binary.op())) {
            boolean and = binary.op() == Hir.BinOp.AND;
            // A conjunction's value being true makes both its operands true; a disjunction's being
            // false makes both false. Neither says anything the other way round.
            Reached left = new Reached(reached.onThen(), reached.onElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            // The right operand runs where the left settled nothing — which is where the left was
            // true under `&&` and false under `||`, and that is what the left's own forced value
            // above says.
            Reached right = new Reached(
                    and && reached.onThen() && reached.trueThen(),
                    !and && reached.onElse() && reached.falseElse(),
                    and && reached.trueThen(), !and && reached.falseElse());
            placed(binary.left(), left, out);
            placed(binary.right(), right, out);
            return;
        }
        if (e instanceof Core.Binary comparison && !combines(comparison.op())) {
            out.add(new Placed(comparison, reached.witness()));
        }
    }


    private static CoverageSites.GuardRef guardOf(CoverageSites.Plan plan, Core.If iff) {
        int[] arms = plan.probesOf(iff);
        if (arms == null || arms.length != 2) {
            return null;
        }
        for (CoverageSites.GuardRef guard : plan.guards()) {
            if (guard.siteIndexThen() == arms[0] && guard.siteIndexElse() == arms[1]) {
                return guard;
            }
        }
        return null;
    }

    /**
     * The number a comparison names, which is a location's content or something taken of it.
     *
     * <p>Which of the standard library's calls count is asked of {@link NumericMeasures} rather than
     * decided here, and asked of the operation the call resolved to rather than of its spelling. The
     * argument has to be a location: {@code List.length(List.map(f, xs))} counts something no path
     * names, and a boundary on it could not be looked for in a row.
     */
    static NumericTerm termOf(Core e, InputReads reads, Symbols symbols) {
        NumericMeasures.Measured measured = NumericMeasures.measureIn(e);
        if (measured != null) {
            TermPath of = reads.pathOf(measured.of(), symbols);
            return of == null ? null : new NumericTerm.SizeOf(measured.operation(), of);
        }
        TermPath path = reads.pathOf(e, symbols);
        return path == null ? null : new NumericTerm.ValueOf(path);
    }


    /** Whether a line can be drawn on what this type carries, asked of the one place that says so. */
    static boolean orderable(Type type, Symbols symbols) {
        return Carrier.ofValue(type, symbols) != null;
    }

    private GuardThresholds() {}
}
