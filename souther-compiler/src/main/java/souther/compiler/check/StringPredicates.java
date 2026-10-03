package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import net.unit8.notation199x.pattern.PatternMeaning;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A library predicate over a string, as the strings it accepts.
 *
 * <p>The one place a call is read as a set of strings. What {@code String.contains("市", value)}
 * says about the position it names is which strings stand there — the same kind of answer
 * {@code String.matches} gives and the same kind this compiler already knows how to hold, since a
 * language over code points is what {@link souther.compiler.regex} is. Read one spelling at a time
 * instead, {@code matches} was a set of strings and the predicates beside it were forms nothing
 * took apart, so a position an author had written a rule for admitted every string there is — and a
 * value nobody could compose there took its siblings' obligations down with it.
 *
 * <p><b>Keyed by what the operation means and not by how a rule is written.</b> Each entry says
 * which argument carries the position, which carries the text, and what the strings around that
 * text may be. A predicate added to the library is a row here or is named as one this does not
 * answer for ({@code EveryPredicateOverAStringIsReadAsASetOfStringsTest}), so a new one does not become
 * a rule that quietly says nothing.
 *
 * <p><b>One clause, one reading, handed on.</b> What a clause states is worked out once, by the
 * entry point its tree has, and comes back as a {@link Reading} that holds what became of it — the
 * strings, or what stopped the reading short of them. A caller takes that value rather than going
 * back to the clause to establish a second time what it already has: asking twice is one question
 * with two derivations, and the day either the fold or the parser learns a form is the day they
 * part.
 *
 * <p><b>And what it says about a position is nobody's answer here.</b> The strings are a fact about
 * a language. Whether the position those strings stand at is restricted, divided, or left where it
 * was found turns on what the rule is written in, and it is settled by the reading that holds every
 * rule reaching the position — so this hands over the strings and stops. Answered here, the same
 * language would mean one thing under an invariant, whose other side is refused at construction, and
 * another under a behavior, where both sides stand.
 *
 * <p>{@code String.isEmpty} is not here, and is not missing. The library writes it as
 * {@code String.length(s) == 0}, so what it states is a question about a number and is answered
 * where numbers are — and not by a table of the sets of strings a call names.
 *
 * <p>What that comes to for a reader is what the library writing an operation in this language
 * comes to everywhere: the reading a rule is taken from keeps the operation standing, so a caller's
 * rule about what {@code String.isEmpty} answers is a rule about a value an operation made. The
 * comparison the library wrote inside it is that operation's, and a caller does not answer for it.
 */
public enum StringPredicates {

    /**
     * The strings a written pattern accepts.
     *
     * <p>The one entry whose text is not text: it is a pattern, and what it accepts is what reading
     * it comes to rather than anything composed here. So it has no shape below, and it is the only
     * entry a reading can stop short of, which is where a pattern this compiler cannot take apart is
     * said to be one.
     */
    MATCHES(Kernel.STRING_MATCHES, null),

    /** The strings that hold the written one somewhere. */
    CONTAINS(Kernel.STRING_CONTAINS, written -> new PatternMeaning.InTurn(List.of(
            PatternMeaning.anything(), PatternMeaning.text(written), PatternMeaning.anything()))),

    /** The strings that begin with it. */
    STARTS_WITH(Kernel.STRING_STARTS_WITH, written -> new PatternMeaning.InTurn(List.of(
            PatternMeaning.text(written), PatternMeaning.anything()))),

    /** The strings that end with it. */
    ENDS_WITH(Kernel.STRING_ENDS_WITH, written -> new PatternMeaning.InTurn(List.of(
            PatternMeaning.anything(), PatternMeaning.text(written))));

    /** What the strings around the written text may be, or null where the text is a pattern. */
    private interface Around {
        PatternMeaning accepting(String written);
    }

    private final Kernel kernel;
    private final Around around;

    StringPredicates(Kernel kernel, Around around) {
        this.kernel = kernel;
        this.around = around;
    }

    /** Which library operation this is. */
    public Kernel kernel() {
        return kernel;
    }

    /**
     * How many arguments the call has.
     *
     * <p>All four take the text first and the subject second, which is the library's own order
     * ({@code String.contains(sub, s)}). Written per entry it would be four chances to disagree
     * with the library about a signature nothing here declares.
     */
    public int arity() {
        return 2;
    }

    /** Which argument names the position the rule is about. */
    public int subject() {
        return 1;
    }

    /** Which argument carries what the author wrote. */
    public int written() {
        return 0;
    }

    /** Whether what is written is a pattern rather than text to be looked for. */
    public boolean takesAPattern() {
        return around == null;
    }

    /**
     * The strings this predicate accepts of a position, given the text written in it.
     *
     * <p>Never asked of {@link #MATCHES}: what a pattern accepts is what reading the pattern comes
     * to, and a caller holding one has already read it.
     */
    public PatternMeaning accepting(String written) {
        if (around == null) {
            throw new IllegalStateException(
                    this + " states a pattern, and what it accepts is the pattern's");
        }
        return around.accepting(written);
    }

    /** The one this kernel is, or null where it is no predicate over strings read here. */
    public static StringPredicates of(Kernel kernel) {
        for (StringPredicates each : values()) {
            if (each.kernel == kernel) {
                return each;
            }
        }
        return null;
    }

    /**
     * What became of reading one predicate as the strings it admits.
     *
     * <p>Kept whole because the reading has readers that want different parts of it. What a rule
     * admits is one answer; that the reading stopped, and at what, is another; and a reader handed
     * only the first would ask for the second by reading the clause again. Which of these
     * distinctions reaches an author is the reader's to settle — what is settled here is that
     * nothing was thrown away before it could.
     */
    public sealed interface Reading {

        /** The strings the predicate admits at the position it is about. */
        record Accepting(PatternMeaning accepts) implements Reading {

            public Accepting {
                if (accepts == null) {
                    throw new IllegalArgumentException(
                            "a reading that finished says which strings it accepts");
                }
            }
        }

        /**
         * The predicate is one of these, and what the author wrote in it is not a string this
         * compiler works out.
         *
         * <p>A rule read as far as the call and no further, which is not the same as a clause that
         * is no predicate of this kind — there a reader has nothing to say, and here it has a
         * position with a rule on it that nothing here turned into strings.
         */
        record WrittenArgumentNotKnown() implements Reading {}
    }

    /**
     * How the text an author wrote in a predicate is reached, where the predicate stands.
     *
     * <p>The one thing that differs between the trees a rule is read off, and the reason it is a
     * capability rather than an entry point per tree. What a predicate means once the text is in
     * hand is one answer ({@link #readingOf}); how the text is reached is a question about names,
     * and which names are in force is the reading of the place the rule stands in. A declaration's
     * clauses are read against what that declaration binds, and a body's rules against what the
     * walk of the body has bound where it stands — and neither of those is something this table
     * knows or should learn.
     *
     * <p><b>Which is what keeps a reader from being weaker than the tree it reads.</b> Written as
     * an entry that folds only what it can see for itself, a rule under {@code let prefix = "JP"}
     * would come back as one whose argument nothing worked out, while the walk that handed it over
     * had the answer. That is a reader declining to take what it was already told, said in the
     * words this compiler uses for a rule it cannot read.
     */
    @FunctionalInterface
    public interface WrittenText {

        /** The string {@code expression} stands for, or null where nothing works one out there. */
        String of(Core expression);
    }

    /**
     * A checked clause's predicate: the argument the rule is about, what reading it came to, and
     * what it states in the words the model states it in.
     *
     * <p>{@code statement} is there exactly where the text an author wrote was worked out, which is
     * every reading but {@link Reading.WrittenArgumentNotKnown} — a rule whose text nothing settled
     * has nothing to be called. Checked here rather than left to a reader, so that a caller holding
     * a reading knows without asking whether there is a statement beside it.
     *
     * @param subject   the argument the rule is about, for a caller that resolves it to a position
     * @param reading   what this compiler made of the strings the predicate states there
     * @param statement what the rule states, for a reader that names what it divides a position
     *                  into. Absent only where the text was not worked out
     */
    public record Stated(Core subject, Reading reading, PredicateStatement statement) {

        public Stated {
            if (subject == null || reading == null) {
                throw new IllegalArgumentException(
                        "a predicate that was stated is about something and was read");
            }
            if ((statement == null) != (reading instanceof Reading.WrittenArgumentNotKnown)) {
                throw new IllegalArgumentException(
                        "a rule states something exactly where its text was worked out: " + reading);
            }
        }
    }

    /**
     * What this predicate says, given the text written in it.
     *
     * <p>Never asked of {@link #MATCHES}. A pattern is not read here: the checker read it and the
     * call carries what it means ({@link #statedBy}), so a tree has one reading of its patterns and
     * it is the checker's.
     */
    private Reading readingOf(String written) {
        return new Reading.Accepting(accepting(written));
    }

    /**
     * What the rules governing {@code named} say about strings, part by part, as the declarations
     * that wrote them publish them.
     *
     * <p>For a reader that proposes a value out of a declaration's rules. The clauses are the ones
     * the checker typed, so a pattern is the meaning the checker settled on the call
     * ({@link #statedBy}) — whatever the author built it out of. Read again off the tree the author
     * wrote, the same rule would have a second reading, and one that could not follow what the
     * checker followed: a pattern written as a value of the module joined to a literal reads there
     * as text nothing worked out.
     *
     * <p>A part is read where it stands. The bindings above it are put in place of the names they
     * give before the text of a predicate is folded, so a rule reached through a helper says what
     * the same rule written out says.
     *
     * <p>Only a part stated outright is a predicate here. A denial and a choice each state
     * something about the strings, and neither is one set of strings to take a value out of.
     */
    public static StatedOn statedOn(TypeSymbol.AtModule named, RuleReadingSource source) {
        Clauses clauses = new Clauses(source);
        Map<PartId<RuleRef.Invariant>, Reading> read = new HashMap<>();
        Set<Clause.Ref> notTyped = new HashSet<>();
        for (ClauseMeaning each : clauses.declared(named)) {
            Clauses.AsStated stated = clauses.stated(each);
            if (stated == null) {
                notTyped.add(each.ref());
                continue;
            }
            for (Clauses.StatedPart part : clauses.partsOf(stated)) {
                Stated said = statedIn(part.of(), source.symbols(), Map.of());
                if (said != null) {
                    read.put(part.id(), said.reading());
                }
            }
        }
        return new StatedOn(read, notTyped);
    }

    /**
     * What the rules governing one declaration say about strings, part by part.
     *
     * @param read     what each part that is a predicate of this kind came to, by the part
     * @param notTyped the clauses the checker has no form for. What their parts say about strings
     *                 is not known, which is not the same as their saying nothing
     */
    public record StatedOn(Map<PartId<RuleRef.Invariant>, Reading> read, Set<Clause.Ref> notTyped) {

        public StatedOn {
            read = Map.copyOf(read);
            notTyped = Set.copyOf(notTyped);
        }

        /** What {@code part} came to, or null where it is no predicate of this kind. */
        public Reading of(PartId<RuleRef.Invariant> part) {
            return read.get(part);
        }

        /** Whether the checker typed the clause {@code part} is a part of. */
        public boolean typed(PartId<RuleRef.Invariant> part) {
            return !notTyped.contains(part.rule().clause());
        }

        /**
         * The pattern {@code part} states, as a rule an author wrote states it, or null where it
         * states none this reads.
         *
         * <p>The one way to come by a {@link StatedPattern}: what this hands out is what a
         * declaration's rule said, and nothing a reader composed on its way to a value.
         */
        public StatedPattern patternOf(PartId<RuleRef.Invariant> part) {
            return read.get(part) instanceof Reading.Accepting it
                    ? new StatedPattern(it.accepts()) : null;
        }
    }

    /**
     * A pattern a rule an author wrote states, as the checker read it.
     *
     * <p>Apart from the patterns a reader composes on its way to a value — the strings of so many
     * characters a count leaves, a meet, a complement — which say the same kind of thing about
     * strings and are not anybody's rule. A reader that holds one of these holds something an
     * author can be sent to; one holding a pattern it built has nobody to send them to. So this is
     * made here, out of what a rule was read to state, and nowhere else ({@link StatedOn#patternOf}).
     *
     * <p>Two of these are one where they state the same strings, whichever rules stated them: two
     * rules writing one pattern are one pattern to build. Which rule it was is the caller's to keep
     * beside it.
     */
    public static final class StatedPattern {

        private final PatternMeaning meaning;

        private StatedPattern(PatternMeaning meaning) {
            if (meaning == null) {
                throw new IllegalArgumentException("a stated pattern states some strings");
            }
            this.meaning = meaning;
        }

        /** The strings it accepts. */
        public PatternMeaning meaning() {
            return meaning;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof StatedPattern it && meaning.equals(it.meaning);
        }

        @Override
        public int hashCode() {
            return meaning.hashCode();
        }

        @Override
        public String toString() {
            return "StatedPattern[" + meaning + "]";
        }
    }

    /**
     * What one shape of a clause states as a predicate of this kind, read under {@code given}, or
     * null where it states none.
     *
     * <p>A binding is crossed by putting what it gives in place of the name, each value read under
     * the bindings above it.
     */
    private static Stated statedIn(ClauseExpr shape, Symbols symbols, Map<BindingId, Core> given) {
        return switch (shape) {
            case ClauseExpr.Scoped scoped -> {
                Map<BindingId, Core> inside = new HashMap<>(given);
                inside.put(scoped.binding().binder().binding(),
                        Clauses.substituted(scoped.binding().value(), given));
                yield statedIn(scoped.body(), symbols, inside);
            }
            case ClauseExpr.Leaf leaf when leaf.positive() -> statedBy(leaf.of(), symbols,
                    e -> Terms.folded(Clauses.substituted(e, given), symbols, Denotations.none())
                            instanceof String written ? written : null);
            case ClauseExpr.Leaf _, ClauseExpr.Joined _ -> null;
        };
    }

    /**
     * The same off a checked clause, or null where it is no predicate of this kind.
     *
     * <p>Beside {@link #statedOn} and in the same file on purpose. One question — which operations
     * say which strings stand at a position — asked of a declaration's published clauses by a reader
     * proposing values, and of the clause in hand by the reading of what a position admits. Every
     * entry point comes down to {@link #statedBy}, so a predicate learned is learned by all of them.
     *
     * <p><b>Reaching the text is the whole of the difference, and it is handed in.</b> What the
     * author wrote is reached through whatever knows the names in force where the rule stands —
     * a declaration's own bindings on one side, the walk of a body on the other — and that is a
     * {@link WrittenText} the caller supplies rather than a fold written here per tree. Written as
     * one entry point per tree, a reader whose fold was the weaker of them would report a rule as
     * one whose argument nothing worked out while holding the answer, and the same rule would mean
     * two things depending on which tree it was read off. Everything past the text is
     * {@link #readingOf} and is one, except a pattern, whose meaning the call carries.
     *
     * <p>The positions below are read off the call without being checked against it, and two things
     * hold that up between them. A {@link Core.PreservedCall} has the arguments its declaration
     * takes, which is the node's own and true of every one that exists. That the numbers this table
     * names are positions such a declaration has is the other half, and it is a fact about this
     * table and the library rather than about any call: where the two disagree, every rule written
     * with the operation is being read at the wrong argument, and which call arrived first is no
     * part of that. So it is not asked here.
     */
    public static Stated statedByChecked(Core clause, Symbols symbols, Terms terms,
                                         Denotations at) {
        return statedBy(clause, symbols,
                e -> Terms.folded(e, symbols, at) instanceof String written ? written : null);
    }

    /**
     * The same off a checked tree, with the text reached however the place the rule stands in
     * reaches it.
     *
     * <p>What {@link #statedByChecked} is, with the one thing that differs handed in. A body's walk
     * knows what its names stand for where the rule is written and a declaration's reading knows
     * what its clauses bound, and neither of those belongs here — what belongs here is that the
     * predicate, the argument it is about and what it means are the same however the text arrived.
     *
     * <p>{@link Reading.WrittenArgumentNotKnown} keeps its meaning through this. It says the
     * predicate was read and the text the author wrote was not worked out, which is a fact about
     * the rule; a caller resolving the argument with less than it holds would be putting a fact
     * about itself under that word.
     *
     * <p><b>A pattern is not read here.</b> The checker read it where it settled the call, and what
     * it means is on the call ({@link Core.PreservedCall#settled}); this takes it from there, so a
     * checked tree has one reading of its patterns and it is the checker's. The text that was
     * handed in is for the predicates that look for text, which is theirs to be read as.
     */
    public static Stated statedBy(Core clause, Symbols symbols, WrittenText text) {
        if (!(Core.withoutStanding(clause) instanceof Core.PreservedCall call)
                || !(call.operation() instanceof ValueName.Stdlib.Operation operation)) {
            return null;
        }
        StringPredicates predicate = of(symbols.kernelOf(operation));
        if (predicate == null) {
            return null;
        }
        Core subject = call.args().get(predicate.subject());
        if (predicate.takesAPattern()) {
            // A kept `String.matches` exists only where its pattern was read, so one without its
            // meaning is the checker's contract broken rather than a rule this could not read.
            if (!(call.settled() instanceof Core.KernelFact.StringMatches settled)) {
                throw new IllegalStateException(
                        "a String.matches call carries the pattern the checker read: " + call);
            }
            return new Stated(subject, new Reading.Accepting(settled.meaning()),
                    new PredicateStatement.Applying(operation.qualified(), settled.written()));
        }
        String written = text.of(call.args().get(predicate.written()));
        // What the model calls the operation, taken off the name the call resolved to rather than
        // from the table. The table is keyed by what an operation means, and what a document calls
        // it is what an author writes — read off a key, a class would be named after this
        // compiler's word for the meaning.
        return written == null
                ? new Stated(subject, new Reading.WrittenArgumentNotKnown(), null)
                : new Stated(subject, predicate.readingOf(written),
                        new PredicateStatement.Applying(operation.qualified(), written));
    }

}
