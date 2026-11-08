package souther.compiler.report;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.cst.CstError;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.GeneratedRowsMessage;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;
import souther.compiler.fmt.Formatter;
import souther.compiler.source.SourceId;
import souther.compiler.publish.PublishedIncompleteness;
import souther.compiler.publish.PublishedRuleHandle;
import souther.compiler.check.Requirements;
import souther.compiler.check.RuleCitation;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.ReportedReason;
import souther.compiler.partition.StringOfferShortfall;
import souther.compiler.publish.RuleHandleProse;
import souther.compiler.diag.Messages;
import souther.compiler.query.Sites;
import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.CaseOfAStatement;
import souther.compiler.partition.CameToNothing;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionShortfall;
import souther.compiler.partition.RepairShortfall;
import souther.compiler.partition.GenerationReason;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.BorderAccount;
import souther.compiler.query.BorderObligationPointAssessment;
import souther.compiler.query.GenerationScope;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.OfferedRow;
import souther.compiler.query.Offering;
import souther.compiler.query.Replacements;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.query.ReplacementAsWritten;
import souther.compiler.query.ReplacementReportAnchor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.SequencedMap;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.Set;

/**
 * Rows a person completes, printed rather than written.
 *
 * <p>The rows go out as rows. Each is written with {@code <?>} where its answer goes, which is what
 * the language writes for a row whose answer is owed: the row parses, the module goes on compiling,
 * and the checker reports the answer as work the author has left. So a block can be pasted whole and
 * answered a row at a time, and what was pasted is source — {@code souther fmt} runs over it, a
 * rename of a field a row names reaches it, and the report keeps saying which rows are still owed
 * an answer.
 *
 * <p>What is commented is the prose. A block carries lines that are not Souther — the {@code ensures}
 * a behavior states, a note over a row composed for more than one thing, a line for each point no row
 * could be written at — and those are written as comments so that the block around them stays
 * something a file can hold.
 *
 * <p>The prose is in the reader's language and the source is not. What a block writes as Souther —
 * the rows, their values and the names they are given — is the same whichever language is named,
 * because it is what an author pastes and keeps; the comments around it are the catalog's, in the
 * language the block is asked for in ({@link Block#text}).
 *
 * <p>Nothing is written to a file. Where the rows belong is a question with a real answer — the
 * module's own source or an attached {@code examples for} file — and one this does not have to guess
 * at, because a person who can read the block can put it where they want it.
 */
public final class GeneratedRows {

    /** How the language writes a row's answer before anyone has written it. Read from the token
     * rather than spelt again: the parser, the formatter and this block say it one way. */
    private static final String UNANSWERED =
            SyntaxKind.UNANSWERED.fixedSpelling().orElseThrow();

    /**
     * A block, and how much of it is rows.
     *
     * <p>Two answers because callers ask two different things of this. What to print is the text; a
     * block of notes and no rows is worth printing, and {@code souther examples --generate} prints
     * it. Whether there is a row to write is {@link #rowCount}, and it is the generator's answer
     * rather than something read off the text: an editor offering "write the rows this does not cover"
     * asked whether the block was blank, and a block that holds only the reason nothing was composed
     * is not blank — so the action appeared, a person took it, and what it wrote into their source
     * was a comment (issue #955).
     *
     * <p>The text is written when it is asked for, in the language it is asked for in. What rows it
     * holds and how many is decided before that and is one answer for every language.
     */
    public static final class Block {

        private final int rowCount;
        private final Function<Locale, String> written;

        private Block(int rowCount, Function<Locale, String> written) {
            if (rowCount < 0) {
                throw new IllegalArgumentException(
                        "a block offering fewer than no rows: " + rowCount);
            }
            this.rowCount = rowCount;
            this.written = Objects.requireNonNull(written,
                    "a block is of something, even if it is empty");
        }

        /** How many rows the block offers, which is what a caller that is about to change
         *  somebody's source has to ask. */
        public int rowCount() {
            return rowCount;
        }

        /** What to print: the rows, and the prose around them in {@code language}. */
        public String text(Locale language) {
            return written.apply(language);
        }

        /** The same with the prose in English, for a reader who reads the block in English. */
        public String textInEnglish() {
            return text(Messages.BASE_LANGUAGE);
        }
    }

    /**
     * The block for a finished compile, for the modules and behaviors the caller asked about.
     *
     * <p>Asked here and not with the rest of a compile's questions, because filling the combinations
     * searches the pair space, and nobody who only wanted the report should pay for that. The rows at
     * the edges cost nothing here: each was built where the boundary was measured, and this reads what
     * that attempt produced.
     *
     * <p>{@code rendering} is what the caller calls its sources, for the same reason the report beside
     * this block asks for it: a note here is read in the same terminal, and a source id is an
     * identity rather than a name.
     */
    public static Block of(Compilation compilation, String module, String behavior,
                           SourceRendering rendering) {
        return of(compilation, rendering, offered(compilation, module, behavior));
    }

    /**
     * What this run offers, one entry per module it was asked about.
     *
     * <p>Asked once and handed to both readers of it. The rows a person is given decide two things
     * — what the block prints, and which input the report sends them to for a line one of those
     * rows answers — and a second asking would compose and run the rows again to arrive at the same
     * answer, free to arrive at another.
     *
     * <p>Which rows go out is settled where both searches are read ({@link Adequacy#offeredFor}):
     * a behavior's own and the ones a declaration's line is owed are work for one person, and a
     * renderer putting them together would be deciding that where the layout is.
     */
    public static Map<String, Offering> offered(Compilation compilation, String module,
                                                String behavior) {
        Map<String, Offering> out = new LinkedHashMap<>();
        for (String name : compilation.modules()) {
            if (module != null && !module.equals(name)) {
                continue;
            }
            Offering offering = Adequacy.offeredFor(compilation.db(),
                    new OfferingRequest(name, behavior == null ? new GenerationScope.Module()
                            : new GenerationScope.Behavior(behavior)));
            if (offering != null) {
                out.put(name, offering);
            }
        }
        return out;
    }

    /** The block for offerings already asked for, which is what a caller that also handed them to
     *  the report has. */
    public static Block of(Compilation compilation, SourceRendering rendering,
                           Map<String, Offering> offered) {
        List<Block> blocks = new ArrayList<>();
        int rows = 0;
        for (Map.Entry<String, Offering> each : offered.entrySet()) {
            Block one = of(each.getValue(), WrittenEnsures.of(compilation.db(), each.getKey()),
                    rendering, compilation.db());
            blocks.add(one);
            rows += one.rowCount();
        }
        return new Block(rows, language -> {
            StringBuilder out = new StringBuilder();
            blocks.forEach(one -> out.append(one.text(language)));
            return out.toString();
        });
    }

    /**
     * What nothing offers a row for among the module's declarations.
     *
     * <p>Read off the same resolutions the rows above were, so the two cannot disagree: a line whose
     * row is printed two lines up is not one this says nothing offers a row for.
     *
     * <p>Which lines this is about was settled where the search was, and is not asked again here. A
     * renderer that filtered by what the behavior carries would be deciding the request's own
     * question a second time, and would be free to decide it differently.
     *
     * <p>Asked of what the walks came to and not of the findings. A finding stands where something
     * has shown a row can be written at the point; a line the search failed at with nothing yet
     * promising a row raises none, and the block would go quiet about work it had just tried — which
     * is the same rule the rows beside these are offered under.
     *
     * <p><b>Which sentence a line gets is the answer's shape and not this reader's choice.</b> What
     * a search of one reading came to is a fact about that reading and is said as one, naming the
     * behavior the way every other note here does. That no row can be written at the line is a
     * claim about every reading of it, and only an answer that passed the gate carries it — so it
     * is said once, under the declaration that drew the line, and cannot be written from evidence
     * that does not support it.
     */
    private static void declarations(StringBuilder out, Offering offering, Page page,
                                     PublishedRuleHandle.WhereARuleIs places) {
        BorderAccount account = offering.account();
        Set<Message> said = new LinkedHashSet<>();
        for (Map.Entry<BorderObligationPoint, BorderAccount.Unmet> each
                : account.unmet().entrySet()) {
            // Nothing about a point one of the rows above stands at. What is left to write is what
            // this says, and a line telling a person no row was composed for something they are
            // being handed a row for is work that is not left.
            if (offering.answered().contains(new ObligationIdentity.OfALine(each.getKey()))) {
                continue;
            }
            switch (each.getValue()) {
                // Said once, of the line, and in the declaration's own words. What each reading
                // proved it of is not repeated: they agree, which is what let this be said at all.
                case BorderAccount.Unmet.TheLineCannotBeWritten(var owedBy, var asked, var _) ->
                        say(out, said, page, new GeneratedRowsMessage.NoRowCanBeWrittenAtTheLine(
                                asked, owedBy, NoValue.standsAtIt()));
                // One line per reading, because they are not one fact: a reading whose rules leave
                // nothing at its own position and one whose search stopped are different news, and
                // a line carrying whichever came first would carry the order the walk took.
                case BorderAccount.Unmet.WhatTheReadingsCameTo(var _, var asked, var came) ->
                        came.forEach(at -> say(out, said, page, switch (at) {
                            case BorderAccount.At.Searched(var reading, var why) ->
                                    new GeneratedRowsMessage.NoRowFor(why.subject(),
                                            reading.behavior(), saidOf(why, page, places));
                            // Said, because a reading that was asked about and could not be
                            // searched is a thing that happened to this run. Left out, a reader
                            // sees the readings that answered and no sign that another was asked.
                            case BorderAccount.At.CouldNotBeSearched(var reading) ->
                                    new GeneratedRowsMessage.NoRowForAnUnsearchedBehavior(asked,
                                            reading.behavior());
                        }));
                case BorderAccount.Unmet.NothingWasSearched(var owedBy, var asked) ->
                        say(out, said, page, new GeneratedRowsMessage.NoRowForOwedBy(
                                asked, owedBy, why(Generator.UnresolvedCombination.Reason
                                        .NO_READING_OF_THE_LINE_COULD_BE_SEARCHED)));
            }
        }
    }

    /**
     * The block for one offering.
     *
     * <p>Which rows go out is settled before this is called and is not decided again here. What
     * this adds is what they are called and how they are laid out — an arm's name is the report's
     * word, and a heading, a note and a comment marker are not things a row carries.
     */
    public static Block of(Offering offering, Map<String, List<String>> ensures,
                           SourceRendering rendering, Db db) {
        // The count leaves with the text. It was worked out here and thrown away, and the one
        // caller that needed it read the text instead.
        return new Block(offering.count(),
                language -> written(offering, ensures, new Page(rendering, language), db));
    }

    /** The block for one offering, with its prose in the language of {@code page}. */
    private static String written(Offering offering, Map<String, List<String>> ensures, Page page,
                                  Db db) {
        PublishedRuleHandle.WhereARuleIs places = cited -> Sites.placeOf(db, cited);
        String module = offering.request().module();
        BorderAccount account = offering.account();
        // Written once and then read three times — printed, counted, and asked whether there is
        // anything to answer. Counting the candidates instead gives a number about work a reader
        // cannot see, and asking the candidates whether the block holds a hole prints the line
        // telling them to fill one over a block that has none.
        Map<String, List<Offered>> offered = named(offering, db, page, places);
        int rows = offering.count();
        StringBuilder out = new StringBuilder();
        if (rows > 0) {
            int suggestions = offering.suggestionCount();
            int owed = rows - suggestions;
            if (suggestions == 0) {
                comment(out, page, rows == 1 ? new GeneratedRowsMessage.OneRowGenerated()
                        : new GeneratedRowsMessage.RowsGenerated(rows));
            } else {
                comment(out, page, new GeneratedRowsMessage.GeneratedBy());
                if (owed > 0) {
                    comment(out, page, owed == 1 ? new GeneratedRowsMessage.OneRowToFill()
                            : new GeneratedRowsMessage.RowsToFill(owed));
                }
                comment(out, page, suggestions == 1
                        ? new GeneratedRowsMessage.OneOptionalRow()
                        : new GeneratedRowsMessage.OptionalRows(suggestions));
            }
            comment(out, page, new GeneratedRowsMessage.ReplaceEachUnanswered(UNANSWERED));
            out.append(stated(blocks(module, offered, page), ensures, page));
        }
        for (Map.Entry<String, Adequacy.Filling> behavior : offering.searched().entrySet()) {
            notes(out, behavior.getKey(), behavior.getValue(), page, offering, places, db);
        }
        // And what the module's declarations are owed that nothing composed a row for. Here rather
        // than after this returns, because what this builds is the block: a caller that rendered
        // through it and appended the rest itself would be a second place that knows what a block
        // holds, and the one that forgot would print rows with nothing said about the work beside
        // them.
        if (account != null) {
            declarations(out, offering, page, places);
        }
        return pastable(module, out.toString());
    }

    /** A line of prose, written as the comment a block holds prose in. */
    private static void comment(StringBuilder out, Page page, Message said) {
        out.append("// ").append(page.say(said)).append(System.lineSeparator());
    }

    /**
     * The block, held to being something a file can take.
     *
     * <p>What the block holds is rows and prose about them, and the marker in front of the prose is
     * the only thing telling them apart. There is a writer for each thing there is to say — the
     * clauses a behavior states, the note over a row composed for more than one thing, a line for
     * each point no row could be written at, a sentence for each combination nothing was composed
     * for — and each of them writes its own marker. One that forgets sends prose out as source, and
     * the block stops compiling the moment somebody pastes it, which is the whole of what it is for.
     *
     * <p>Asked by parsing what is left when the prose is taken away, rather than by looking at how
     * a line starts. A shape read off the front of a line is a guess about what the language
     * admits, and the guess a reader would reach for lets exactly the writer this is here for
     * through: a clause is quoted indented, so prose that lost its marker looks like the lines a
     * wrapped row continues on. What the block promises is that a file can take it, and the thing
     * that answers that is the parser.
     *
     * <p>The header goes back on for the reading. It is taken off the block because where the rows
     * are pasted is the author's choice, and a bare {@code example} block is not a file — so the
     * question is asked of the file the block becomes rather than of a fragment nothing accepts.
     */
    private static String pastable(String module, String block) {
        StringBuilder source = new StringBuilder("examples for ").append(module).append("\n\n");
        for (String line : block.lines().toList()) {
            if (!line.startsWith("//")) {
                source.append(line).append("\n");
            }
        }
        List<CstError<?>> refused = CstParser.parse(source.toString()).errors();
        if (!refused.isEmpty()) {
            throw new IllegalStateException("a block goes out as something a file can take, and"
                    + " what is left of this one when its prose is taken away does not parse: "
                    + refused.getFirst() + " in\n" + source);
        }
        return block;
    }

    /**
     * How the note about a finding no strategy composes a row for opens, for what is missing.
     *
     * <p>Not one opening for all of them. Where what is missing is a way to steer a row somewhere,
     * no row in this block was composed for the finding. An output case is not reached by steering
     * at all: rows are composed for what the inputs divide into, and one of them may well answer
     * with the case once it runs — so what is said is that nothing aims a row at it, and nothing
     * about the rows above.
     */
    private static Message openingFor(GenerationOutcome.NotSupported.Reason why, Message what,
                                      String behavior, Message said) {
        return switch (why) {
            case NO_WAY_INTO_THIS_ARM_CAN_BE_NAMED, THE_WAYS_INTO_THIS_ARM_ARE_NOT_ENUMERABLE,
                 THE_WAYS_INTO_THIS_ARM_ARE_NOT_TOLD_APART, MORE_WAYS_IN_THAN_THE_READING_HOLDS, THE_ARM_RUNS_WHERE_SOMETHING_CALLS_IT,
                 A_CONSTRUCTION_DECIDES_THIS_ARM, NO_AXIS_AT_THIS_POSITION ->
                    new GeneratedRowsMessage.NothingOffersARowFor(what, behavior, said);
            case NO_STRATEGY_FOR_AN_OUTPUT_CASE, NO_STRATEGY_FOR_A_WEIGHT ->
                    new GeneratedRowsMessage.NothingAimsARowAt(what, behavior, said);
        };
    }

    /**
     * The findings this block owes a reader a word about.
     *
     * <p>A point of a border is said like everything else. What a run offers is the account's, and
     * the points are obligations of it: a block that held them back read as though the arms and the
     * cases were all there was to write, and the report beside it went on naming what the block had
     * decided not to mention.
     *
     * <p>A finding row synthesis is not about is left out. This block is rows to write and notes
     * about rows that could not be written; a measure this compiler could not make has no row
     * waiting behind it, and a line here saying nothing offers one would put our own shortfall in
     * a list of the author's work. The report says those findings, which is where they belong.
     */
    private static List<Adequacy.GenerationDisposition> shown(Adequacy.Filling filling,
                                                              Offering offering) {
        return filling.generation().stream()
                .filter(each -> !(each.outcome() instanceof GenerationOutcome.NotApplicable))
                // And nothing about something one of the rows above stands at. What the search for
                // this finding came to is what it came to, and a person reading the block is being
                // told what is left to write — which a row in front of them is not.
                .filter(each -> each.item().stream()
                        .noneMatch(offering.answered()::contains))
                .toList();
    }

    /**
     * One row as it will be written, and everything it was composed for.
     *
     * <p>One name is a name and several are a note apiece over a row with none. Joining them into
     * one name is the way of being wrong that reads worst: {@code "a x b"} reads as one thing owed
     * at two positions at once, which is the shape this whole block was written against. The
     * language lets a row be written without a name and an author names it when they answer it;
     * what it is for is said in words above it, once per thing.
     *
     * <p>Which of those it is named by is decided over the whole block and not by the row alone.
     * A name is short words with no place in them, since it stays in the source where a place
     * would go stale; two things owed at two forks can be called the same, and a row named by such
     * words would be named for either. So a row takes a name only where it was composed for one
     * thing and no other thing in its block is called by the same words — and otherwise says over
     * itself, with the place, each thing it was composed for.
     *
     * <p>What else the row is handed for is said over it, named or not. A line it stands at or a
     * rewrite it tells apart is the run's to give and to take back — another row can meet the
     * line — so it decides nothing about the name, and a name that came and went with it would
     * rename a row nothing about which had changed.
     *
     * @param inputs  the row's values, in the form they are written in
     * @param name    the one thing it was composed for, where that thing's name tells it from every
     *                other thing in the block
     * @param besides everything else it is for, in the order it was taken: what it was composed
     *                for where no name was given, and then what it is handed for
     * @param suggested whether the row is offered only to try an input, so that nothing uncovered
     *                waits on it
     * @param stops   where the row stops and what looking for one that goes further came to, in
     *                this layer's words, one sentence per search that took it no further than a
     *                guard
     */
    private record Offered(String inputs, String standsIn, Optional<Called> name,
                           List<Called> besides, List<String> stops, boolean suggested) {

        Offered {
            besides = List.copyOf(besides);
            stops = List.copyOf(stops);
            if (name.isPresent() && name.get().name().isEmpty()) {
                throw new IllegalArgumentException("a row is named for a thing that has a name: "
                        + name.get());
            }
            if (name.isPresent() && besides.stream()
                    .anyMatch(each -> each.owed().equals(name.get().owed()))) {
                throw new IllegalArgumentException("what names a row is not said over it again: "
                        + name.get());
            }
        }

        /** The row as it is written: named where one thing names it, and not otherwise. What else
         *  it is for is said over it ({@link #blocks}) rather than in it — the formatter parses
         *  what it is handed, and prose is not a row. */
        String written() {
            // The name as the language writes a string, because that is what it is. Written out as
            // it stands, a name holding a quote — which a class named after a rule about strings
            // does — closes the literal early and the rest of it becomes source.
            return name.map(thing -> "    | " + CstLexer.literalOf(thing.name().orElseThrow())
                            + " : (" + inputs + ")" + standsIn + " -> " + UNANSWERED)
                    .orElse("    | (" + inputs + ")" + standsIn + " -> " + UNANSWERED);
        }

        /** What to say over the row: all it is for but what its name already says. */
        List<String> saidOver(Page page) {
            return besides.stream().map(each -> each.placed(page)).toList();
        }
    }

    /**
     * Which thing a row is composed for or a note is about, apart from what it is called.
     *
     * <p>Words are not this. Two things owed at two forks of code this build holds no source of
     * are called alike and placed alike, and counted by their words they were one. So what is one
     * thing and what is two is asked of this and never of the words.
     */
    private sealed interface Owed {

        /** A thing a finding is about that is owed a row: the obligation's own identity, which
         *  several places the same thing stands at share. */
        record AnObligation(ObligationIdentity identity) implements Owed {}

        /** A finding about something no obligation is: the finding itself. */
        record AFinding(About about) implements Owed {}

        /** A purpose that names itself, one per label it carries. */
        record ALabel(Generator.Purpose purpose, String label) implements Owed {}

        /** What {@code finding} is about. */
        static Owed by(Adequacy.Finding finding) {
            return finding.about() instanceof About.OfAnObligation owed
                    ? new AnObligation(owed.obligationIdentity())
                    : new AFinding(finding.about());
        }
    }

    /**
     * What one thing a row is composed for is called in this block, and where it is.
     *
     * <p>Apart, because they are put in different places. {@code words} with no place are what a
     * row may be named by, where they are short words that are the thing's own: a name stays in the
     * source, so it carries no place, which would go stale as the source moves. A comment says both,
     * where the place is read once and is what tells two things of the same words apart. A thing
     * with no place to give has none.
     *
     * <p>Not every thing has a name. A decision rule and a combination of decisions are told apart
     * by every condition they turn on, and each condition is a place; their words say what kind of
     * thing it is and the conditions are the place, so a row is never named by them.
     *
     * <p>A name is source and the rest is prose. The words a row is named by are written in the
     * base wording, so that the block a reader pastes is the same whichever language they read the
     * comments in; the words a comment says are in the comment's language.
     *
     * @param owed  which thing it is, which is what decides whether two of these are one
     * @param words what it is called, in the language of the page this is said on
     * @param name  the words a row may be named by, in the base wording, where they name the
     *              thing
     * @param place where it is, in the words of the page this is said on
     */
    private record Called(Owed owed, Message words, Optional<String> name, Optional<String> place) {

        Called {
            Objects.requireNonNull(owed, "a thing a row is for is some thing");
            Objects.requireNonNull(words, "and is called something");
            Objects.requireNonNull(name, "and is named, or is not");
            Objects.requireNonNull(place, "and is somewhere, or nowhere it can say");
        }

        /** A thing a row may be named by {@code name}, at {@code place}. */
        static Called named(Owed owed, Message words, String name, Optional<String> place) {
            return new Called(owed, words, Optional.of(name), place);
        }

        /** A thing no row is named by. */
        static Called unnamed(Owed owed, Message words, Optional<String> place) {
            return new Called(owed, words, Optional.empty(), place);
        }

        /** The words and the place, as a comment over a row says them. */
        String placed(Page page) {
            return page.say(place.<Message>map(at -> new GeneratedRowsMessage.Placed(words, at))
                    .orElse(words));
        }

        /** The same, with a name marked as the words it is, as a note under a block says it. */
        String quoted(Page page) {
            return page.say(quoted());
        }

        /** The same as a message, for a line that is told apart by what it says. */
        Message quoted() {
            Message said = name.isPresent() ? new GeneratedRowsMessage.Quoted(words) : words;
            return place.<Message>map(at -> new GeneratedRowsMessage.Placed(said, at))
                    .orElse(said);
        }
    }

    /**
     * What a finding is called in this block: the words the report writes for what it is about,
     * and where the report sends a reader for it.
     *
     * <p>The place of an arm and of a rewrite of one is the one the finding is shown at
     * ({@link Adequacy#placeOf}), and not one worked out here. A rewrite of an arm this build holds
     * no source of is shown at the behavior, which is not where its fork is, so it is said by the
     * definition that wrote the fork instead.
     *
     * <p>A decision rule and a combination of decisions are said by the conditions the report says
     * them by ({@link AdequacyReport#conditionsOf}, {@link AdequacyReport#waysOf}) — the one
     * reading of each for both — and have no name: every condition is a place.
     */
    private static Called called(Adequacy.Finding finding, Db db, String module, Page page,
                                 PublishedRuleHandle.WhereARuleIs places) {
        SourceRendering rendering = page.rendering();
        Owed owed = Owed.by(finding);
        Message words = about(finding, page, places);
        // The name in the base wording throughout, parts and all: a name is source, and source is
        // the same whichever language the comments around it are in.
        String name = Page.inTheDocument(about(finding, page.base(), places));
        // The place as the report writes it: the position alone in the module's own file, and the
        // file with it in another's.
        SourceId declaredIn = Compilation.sourceIdOf(db, module);
        return switch (finding.about()) {
            case About.AnArmNoRowGoesThrough _ -> Called.named(owed, words, name, Optional.of(
                    Adequacy.placeOf(db, module, finding).said(rendering, declaredIn)));
            case About.ARewriteNoRowTellsApart(var behavior, ReplacementAsWritten.OfAnArm rewrite,
                    var reportAt, var _, var _) -> Called.named(owed, words, name, Optional.of(page.say(
                    switch (reportAt) {
                        case ReplacementReportAnchor.AtTheFork _ -> new ReportMessage.Then(
                                new ReportMessage.Verbatim(Adequacy.placeOf(db, module, finding)
                                        .said(rendering, declaredIn)),
                                RewriteVocabulary.apart(Replacements.toldApartBy(db, module,
                                        behavior, rewrite)));
                        case ReplacementReportAnchor.AtTheBehavior _ -> new ReportMessage.Then(
                                RewriteVocabulary.outOfSight(rewrite, module),
                                RewriteVocabulary.apart(Replacements.toldApartBy(db, module,
                                        behavior, rewrite)));
                        case ReplacementReportAnchor.AtTheWalk _ -> throw new IllegalStateException(
                                "a rewrite of an arm shown at a walk: " + rewrite);
                    })));
            // A fold's rewrite by the fold's place, or by the definition that wrote it where this
            // build holds no source of it, for the reason an arm's is.
            case About.ARewriteNoRowTellsApart(var behavior, ReplacementAsWritten.OfAWalk rewrite,
                    var reportAt, var _, var _) -> Called.named(owed, words, name, Optional.of(page.say(
                    switch (reportAt) {
                        case ReplacementReportAnchor.AtTheWalk _ -> new ReportMessage.Then(
                                new ReportMessage.Verbatim(Adequacy.placeOf(db, module, finding)
                                        .said(rendering, declaredIn)),
                                RewriteVocabulary.apart(Replacements.toldApartBy(db, module,
                                        behavior, rewrite)));
                        case ReplacementReportAnchor.AtTheBehavior _ -> new ReportMessage.Then(
                                RewriteVocabulary.outOfSight(rewrite, module),
                                RewriteVocabulary.apart(Replacements.toldApartBy(db, module,
                                        behavior, rewrite)));
                        case ReplacementReportAnchor.AtTheFork _ -> throw new IllegalStateException(
                                "a rewrite of a walk shown at a fork: " + rewrite);
                    })));
            // A body that decides nothing has one rule and it turns on no condition, so there is
            // no place to say it at.
            case About.ARuleNoRowTakes(var behavior, var ruled) -> {
                List<AdequacyReport.ShownCondition> way = AdequacyReport.conditionsOf(db, module,
                        AdequacyReport.placesFor(db, module, behavior), ruled);
                yield Called.unnamed(owed, new GeneratedRowsMessage.ADecisionRule(),
                        way.isEmpty() ? Optional.empty()
                                : Optional.of(said(way, declaredIn, page)));
            }
            // A point of a line is said with the rule that drew it, which is its place; and points
            // coincide, so no row is named for one.
            case About.APointOfABorder _, About.APointOfADeclaredBorder _ ->
                    Called.unnamed(owed, words, Optional.empty());
            case About.ACombinationNoRowMakes(var combination) -> {
                InteractionEvidence meetings = Objects.requireNonNull(
                        db.ask(new Adequacy.Interacts(module)).value(),
                        "a combination no row makes was measured").get(combination.behavior());
                List<String> ways = AdequacyReport.waysOf(db, module,
                                AdequacyReport.placesFor(db, module, combination.behavior()),
                                meetings, combination).stream()
                        .map(way -> said(way, declaredIn, page)).toList();
                String said = ways.getLast();
                for (int i = ways.size() - 2; i >= 0; i--) {
                    said = page.say(new GeneratedRowsMessage.OrElse(ways.get(i), said));
                }
                yield Called.unnamed(owed, new GeneratedRowsMessage.ACombinationOfTheDecisions(),
                        Optional.of(said));
            }
            default -> Called.named(owed, words, name, Optional.empty());
        };
    }

    /** What a case a statement of the decision draws inside itself is, said in a few words. */
    private static Message wordsOf(CaseOfAStatement which) {
        return switch (which) {
            case CaseOfAStatement.Search(var _, var step) -> switch (step) {
                case AT_THE_NODE -> new GeneratedRowsMessage.ASearchThatFindsItAtTheNode();
                case BELOW_IT -> new GeneratedRowsMessage.ASearchThatFindsItBelowTheNode();
                case NOWHERE_AT_A_LEAF -> new GeneratedRowsMessage.ASearchThatFindsNothingAtALeaf();
                case NOWHERE_BELOW -> new GeneratedRowsMessage.ASearchThatFindsNothingBelow();
            };
            case CaseOfAStatement.KeyOrder(var _, var _, var way) -> switch (way) {
                case HOLDS_BY_THE_LAST -> new GeneratedRowsMessage.AKeyHeldTwiceThatHolds();
                case FAILS_BY_THE_LAST -> new GeneratedRowsMessage.AKeyHeldTwiceThatFails();
            };
        };
    }

    /** The conditions of one way, as the report says each, in their order. */
    private static String said(List<AdequacyReport.ShownCondition> way, SourceId declaredIn,
                               Page page) {
        return AdequacyReport.reasons(page, way.stream()
                .map(each -> AdequacyReport.said(each, declaredIn, page)).toList());
    }

    /**
     * What each thing of one behavior a row may be composed for is called: an arm by the probe the
     * plan gave it, and a rewrite, a decision rule and a combination of decisions by the obligation
     * each is.
     *
     * <p>Read off the findings the generation answers, which is where what they are is already
     * written. A thing the search composed a row for is one a finding named, the plan being made of
     * them, so there are words here for every one a row is offered for.
     */
    private record WhatTheFindingsCall(String behavior, Map<ArmProbe, Called> arms,
                                       Map<ObligationIdentity, Called> owed) {

        static WhatTheFindingsCall in(String behavior, Adequacy.Filling filling, Db db,
                                      String module, Page page,
                                      PublishedRuleHandle.WhereARuleIs places) {
            Map<ArmProbe, Called> arms = new LinkedHashMap<>();
            Map<ObligationIdentity, Called> owed = new LinkedHashMap<>();
            // A behavior with no search of its own composed a row a declaration is owed and nothing
            // else, so there is nothing here to be called anything.
            if (filling != null) {
                for (Adequacy.GenerationDisposition each : filling.generation()) {
                    switch (each.finding().about()) {
                        case About.AnArmNoRowGoesThrough(var arm) -> arms.put(arm.index(),
                                called(each.finding(), db, module, page, places));
                        case About.ARewriteNoRowTellsApart rewrite -> owed.put(
                                rewrite.obligationIdentity(),
                                called(each.finding(), db, module, page, places));
                        case About.ARuleNoRowTakes rule -> owed.put(rule.obligationIdentity(),
                                called(each.finding(), db, module, page, places));
                        case About.ACombinationNoRowMakes combination -> owed.put(
                                combination.obligationIdentity(),
                                called(each.finding(), db, module, page, places));
                        default -> { }
                    }
                }
            }
            return new WhatTheFindingsCall(behavior, arms, owed);
        }

        /** Every thing the findings name, whether or not a row is for it. */
        Stream<Called> all() {
            return Stream.concat(arms.values().stream(), owed.values().stream());
        }

        /**
         * What a row composed for {@code purposes} is for, one thing per purpose and in their
         * order, and without one thing twice.
         *
         * <p>Every one of them and not a name made by joining them. A row that answers two arms
         * answers two things, and `a x b` spelt over the pair reads as an obligation nobody raised
         * — the same fault as naming a row for everything it turns out to settle, arriving from the
         * other side.
         *
         * <p>A thing nothing named is left out, which leaves the row unnamed where it was for that
         * alone: the state of a row nobody has named yet, which is what the language writes for
         * one. Words invented here would be a second vocabulary for it.
         */
        List<Called> of(List<Generator.Purpose> purposes) {
            SequencedMap<Owed, Called> out = new LinkedHashMap<>();
            for (Generator.Purpose purpose : purposes) {
                switch (purpose) {
                    case Generator.Purpose.ForAnArm(ArmProbe probe) -> {
                        if (arms.containsKey(probe)) {
                            out.putIfAbsent(arms.get(probe).owed(), arms.get(probe));
                        }
                    }
                    case Generator.Purpose.ForAReplacement(var rewrite) -> add(out,
                            new ObligationIdentity.OfAReplacement(behavior,
                                    rewrite.replacement()));
                    case Generator.Purpose.ForADecisionRule(var rule) -> add(out,
                            new ObligationIdentity.OfADecisionRule(behavior, rule));
                    case Generator.Purpose.ForACombinationOfDecisions(var settled) -> add(out,
                            new ObligationIdentity.OfACombinationOfDecisions(behavior, settled));
                    // No finding names a case: the decision's measure is short of it, and the
                    // words are the ones a case has, with no place to send a reader to.
                    case Generator.Purpose.ForACaseOfAStatement(var which) -> {
                        Owed owed = new Owed.AnObligation(
                                new ObligationIdentity.OfACaseOfAStatement(behavior, which));
                        out.putIfAbsent(owed, Called.unnamed(owed, wordsOf(which),
                                Optional.empty()));
                    }
                    case Generator.Purpose.ForAClass _, Generator.Purpose.ForAFallbackPairCell _,
                            Generator.Purpose.ForAPoint _, Generator.Purpose.Unstated _ ->
                            purpose.labels().forEach(label -> {
                                Owed owed = new Owed.ALabel(purpose, label);
                                out.putIfAbsent(owed, Called.named(owed,
                                        new ReportMessage.Verbatim(label), label,
                                        Optional.empty()));
                            });
                }
            }
            return List.copyOf(out.values());
        }

        /** The thing {@code identity} is, where a finding named it, or null. */
        Called of(ObligationIdentity identity) {
            return owed.get(identity);
        }

        /** The thing {@code identity} is, where a finding named it. */
        private void add(SequencedMap<Owed, Called> out, ObligationIdentity identity) {
            Called thing = of(identity);
            if (thing != null) {
                out.putIfAbsent(thing.owed(), thing);
            }
        }
    }

    /**
     * The rows this run offers, each with the things it was composed for, in this layer's words.
     *
     * <p>Which rows go out and what each was composed for is {@link Offering}'s; what those things
     * are called is this layer's. An arm is named by the report ({@link ArmVocabulary}) and a
     * generation spells no name for one, so the two are joined here.
     *
     * <p>Which rows are named is asked of the block once every row's things are known: a name
     * another thing in the block is also called by would name either of them ({@link Offered}).
     */
    private static Map<String, List<Offered>> named(Offering offering, Db db, Page page,
                                                    PublishedRuleHandle.WhereARuleIs places) {
        String module = offering.request().module();
        Map<ObligationIdentity, Called> lines = linesOf(offering, page, places);
        Map<String, List<Offered>> out = new LinkedHashMap<>();
        offering.rowsByBehavior().forEach((behavior, rows) -> {
            WhatTheFindingsCall called = WhatTheFindingsCall.in(behavior,
                    offering.searched().get(behavior), db, module, page, places);
            // What each row was composed for, and apart from it the lines and rewrites it is the
            // row a person is handed for. A row is never composed for a line — what a line is owed
            // is answered in the account — and a row composed for something else may be the one a
            // rewrite is answered by, so those come from the offering's answer of where each is
            // shown. Only the first can name the row.
            List<List<Called>> composed = rows.stream()
                    .map(row -> called.of(row.namedFor())).toList();
            List<List<Called>> handed = new ArrayList<>();
            for (int i = 0; i < rows.size(); i++) {
                SequencedMap<Owed, Called> these = new LinkedHashMap<>();
                for (ObligationIdentity item : offering.shownOver(rows.get(i).key())) {
                    Called thing = item instanceof ObligationIdentity.OfALine ? lines.get(item)
                            : called.of(item);
                    if (thing != null) {
                        these.putIfAbsent(thing.owed(), thing);
                    }
                }
                composed.get(i).forEach(thing -> these.remove(thing.owed()));
                handed.add(List.copyOf(these.values()));
            }
            // Each name, and every thing of the behavior it is the name of: what the rows are for,
            // and every thing a finding of it names whether or not a row was composed for it. A
            // name is unique only against all of them, since the report and the notes below the
            // block say the ones with no row under the same words.
            Map<String, Set<Owed>> byName = new HashMap<>();
            Stream.of(composed.stream().flatMap(List::stream), handed.stream().flatMap(List::stream),
                            called.all())
                    .flatMap(each -> each)
                    .forEach(thing -> thing.name().ifPresent(name -> byName
                            .computeIfAbsent(name, _ -> new HashSet<>()).add(thing.owed())));
            List<Offered> here = new ArrayList<>();
            for (int i = 0; i < rows.size(); i++) {
                OfferedRow row = rows.get(i);
                List<Called> forIt = composed.get(i);
                Optional<Called> name = forIt.size() == 1 && forIt.getFirst().name()
                        .map(words -> byName.get(words).size() == 1).orElse(false)
                        ? Optional.of(forIt.getFirst()) : Optional.empty();
                List<Called> besides = new ArrayList<>(name.isPresent() ? List.of() : forIt);
                besides.addAll(handed.get(i));
                // Whose search a stop was said only where the row is for more than one thing: a row
                // for one already says, by its name or over it, which requirement it was looked
                // for.
                boolean several = forIt.size() + handed.get(i).size() > 1;
                List<String> stops = new ArrayList<>();
                for (RepairShortfall stop : row.stops()) {
                    stops.add(stoppedShort(stop, several, db, page, places));
                }
                here.add(new Offered(row.key().inputs(), standingIn(module, row), name, besides,
                        stops, offering.isSuggestion(row.key())));
            }
            out.put(behavior, List.copyOf(here));
        });
        return out;
    }

    /**
     * What each point of a line this offering answers for is called: a body's own lines and its
     * declarations' alike, whichever module declares the type a declaration's line is of.
     *
     * <p>Asked of the account and not of the findings. A point no row is written at is undecided
     * rather than a finding, and is a point a row here is handed for all the same; and the account
     * holds every point the offering answers for, in the words the report says each in — the rule
     * that drew a body's line, and what a declaration wrote its own line on.
     *
     * <p>No name. A point's words are its place, and points coincide: which one a row is handed
     * for is what changes when something else is written.
     */
    private static Map<ObligationIdentity, Called> linesOf(Offering offering, Page page,
                                                           PublishedRuleHandle.WhereARuleIs places) {
        Map<ObligationIdentity, Called> out = new LinkedHashMap<>();
        if (offering.account() == null) {
            return out;
        }
        offering.account().resolved().forEach((point, answer) -> {
            ObligationIdentity line = new ObligationIdentity.OfALine(point);
            Message words = answer.declaredAxis() == null
                    ? about(answer.point(), page, places)
                    : new ReportMessage.Verbatim(answer.said());
            out.put(line, Called.unnamed(new Owed.AnObligation(line), words, Optional.empty()));
        });
        return out;
    }

    /**
     * The {@code with} clause a row carries, or nothing where it stands nothing in.
     *
     * <p>A projection and not a decision. Which of the two things that answer a dependency answers
     * this one was settled where the row was composed, and is read here rather than decided again.
     * A row leaning on the module's table writes nothing at that dependency — the table is already
     * in the file the row is pasted into, and a {@code with} put there would take the row out of
     * the environment every written row of the module runs in.
     *
     * <p>The dependency spelled the way a person writes one, asked of the rule that answers it
     * ({@link Requirements#writtenIn}). A behavior another module declares is reachable through
     * that module whether or not an import brought its bare name in, so a block that wrote the bare
     * name would hand a person a row naming a behavior nothing resolves — and the hint that says
     * what to type and the skeleton that types it would be two answers to one question.
     */
    private static String standingIn(String module, OfferedRow row) {
        List<String> written = new ArrayList<>();
        for (StoodInAnswer each : row.answers()) {
            if (each instanceof StoodInAnswer.OnTheRow(var dependency, var value)) {
                written.add(Requirements.writtenIn(module, dependency) + " = " + value.text());
            }
        }
        return written.isEmpty() ? "" : " with " + String.join(", ", written);
    }

    /**
     * The rows as source, in the form the formatter writes them.
     *
     * <p>Formatted rather than printed straight, because these lines are meant to be pasted into a
     * file that {@code souther fmt} then runs over. A block that came out in a shape the formatter
     * would change turns a paste into a diff on the next commit.
     */
    private static String blocks(String module, Map<String, List<Offered>> offered, Page page) {
        StringBuilder source = new StringBuilder();
        source.append("examples for ").append(module).append("\n");
        for (Map.Entry<String, List<Offered>> behavior : offered.entrySet()) {
            if (behavior.getValue().isEmpty()) {
                continue;
            }
            source.append("\n").append("example ").append(behavior.getKey()).append("\n");
            for (Offered row : behavior.getValue()) {
                source.append(row.written()).append("\n");
            }
        }
        String written = source.toString();
        String formatted;
        try {
            formatted = Formatter.format(written);
        } catch (RuntimeException _) {
            formatted = written;   // a row the formatter cannot read is still a row worth printing
        }
        // The header was there to make the rows parseable on their own. Where they are pasted is the
        // author's choice — the module's own file or an attached one — and only one of those wants it.
        return fills(formatted.replaceFirst("^examples for \\S+\\R+", ""), offered, page);
    }

    /**
     * What each row with more than one thing to its name is for, said over it.
     *
     * <p>Written as a comment, because it is prose and the rows around it are source. Put in after
     * the formatter has run, for the reason the {@code ensures} headings are: what {@link #blocks}
     * hands the formatter is the rows, and what a reader is told about them is not one of them.
     *
     * <p>Matched by position rather than by reading the line. The rows go in in one order and come
     * out in it, and a row the formatter wrapped is still one row — its continuations are indented
     * past the {@code |} that starts it, so what starts a row is what a row starts with.
     *
     * <p>And where the row stops at a guard nothing found a way past, which guard and what each way
     * came to, over the row and not among the notes below the block. The notes are about places no
     * row was found for; this row is offered, and a reader completing it is the one who needs to
     * know it does not get past the guard.
     */
    private static String fills(String rows, Map<String, List<Offered>> offered, Page page) {
        List<Offered> inOrder = new ArrayList<>();
        offered.values().forEach(inOrder::addAll);
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (String line : rows.lines().toList()) {
            if (line.startsWith(ROW) && at < inOrder.size()) {
                Offered row = inOrder.get(at++);
                if (row.suggested()) {
                    comment(out, page, new GeneratedRowsMessage.SuggestedInput());
                }
                for (String each : row.saidOver(page)) {
                    comment(out, page, new GeneratedRowsMessage.Fills(each));
                }
                for (String each : row.stops()) {
                    comment(out, page, new GeneratedRowsMessage.StopsAt(each));
                }
            }
            out.append(line).append(System.lineSeparator());
        }
        return out.toString();
    }

    /** How a row starts, which is how one is told from the lines a wrapped one continues on: those
     *  are indented past it. */
    private static final String ROW = "    | ";

    /**
     * The clauses each behavior carries, put over the rows they are about.
     *
     * <p>Over the rows and not beside each one. A clause is written on the behavior, so it says the
     * same thing about every row of it, and a copy per row would be the same words as many times as
     * the generator happened to offer questions.
     *
     * <p>Put in after {@link #blocks} and not inside it, because these lines are not rows. What that
     * builds is source, written so that {@code souther fmt} would leave it alone; a heading is prose
     * and is written as a comment, and the formatter parses what it is handed.
     */
    private static String stated(String source, Map<String, List<String>> ensures, Page page) {
        StringBuilder out = new StringBuilder();
        for (String line : source.lines().toList()) {
            // The heading a behavior's rows are written under, which is the one line of the block
            // that names a behavior. A row is written indented and under it, so nothing else here
            // can be read for one.
            String behavior =
                    line.startsWith("example ") ? line.substring("example ".length()) : null;
            List<String> clauses =
                    behavior == null ? List.of() : ensures.getOrDefault(behavior, List.of());
            if (!clauses.isEmpty()) {
                // The words the author put in the declaration, quoted whether or not the checker
                // could make a rule of them: what is claimed is that they are written, and nothing
                // further.
                comment(out, page, new GeneratedRowsMessage.EnsuresWrittenFor(behavior));
                for (String clause : clauses) {
                    for (String each : clause.lines().toList()) {
                        out.append("//     ").append(each).append(System.lineSeparator());
                    }
                }
                out.append(System.lineSeparator());
            }
            out.append(line).append(System.lineSeparator());
        }
        return out.toString();
    }

    /**
     * What could not be written, said rather than left out — and said once.
     *
     * <p>A block that printed only the rows it managed would read as though it had filled everything.
     * One that printed a line per combination would say the same thing hundreds of times: a position
     * nothing can write a value for makes every combination it takes part in unfillable, and the
     * position is the fact while the combinations are arithmetic on it.
     *
     * <p>A generation that ended and one that carried on without a position are said apart. This
     * printed {@code generation stopped} over whatever it was given, which is a claim about the run
     * taken from the presence of a reason — and where some positions were read and others were not,
     * the rows it was offering were printed two lines above the line saying it had stopped.
     */
    private static void notes(StringBuilder out, String behavior, Adequacy.Filling filling,
                              Page page, Offering offering,
                              PublishedRuleHandle.WhereARuleIs places, Db db) {
        String module = offering.request().module();
        Set<Message> said = new LinkedHashSet<>();
        // What is said about each finding, kept apart by the finding: two findings can be said in
        // the same words, and they are still two.
        Set<Said> saidOf = new HashSet<>();
        // What each place a row was looked for came to, and what the search met of this compiler's
        // where it met anything. This is where a class says what it came to, so a stop that named
        // no figure here named one nowhere.
        // Joined under what the line shows, so two searches the line cannot tell apart are one
        // line holding what both met rather than one line twice with half of it apiece.
        for (CameToNothing each : CameToNothing.joinedAsShown(filling.composed().unresolved(),
                GeneratedRows::shownForWhatItIsAbout)) {
            say(out, said, page, new GeneratedRowsMessage.NoRowFor(
                    each.why().subject(), behavior, saidOf(each, page, places)));
        }
        // And the points, whose figures are said at the point's own account in the report rather
        // than here. Written with the same clause, one figure would reach a reader twice.
        for (Generator.UnresolvedCombination each : filling.boundaries().unresolved()) {
            say(out, said, page, new GeneratedRowsMessage.NoRowFor(each.subject(),
                    behavior, saidOf(each, page, places)));
        }
        // Every finding a row could answer, and not only the ones a strategy took. One printed in
        // the report and left out of this block is one an author is told nothing about, while the
        // rows above it read as though they filled everything.
        for (Adequacy.GenerationDisposition each : shown(filling, offering)) {
            switch (each.outcome()) {
                case GenerationOutcome.Generated _ -> { }
                // Each of what was tried, because they are not one fact: a combination the model
                // refuses and one the search stopped at are different news, and a line carrying
                // whichever came first carried the order the cells were walked in.
                // Named for the finding and not for where the search went. A class's own search is
                // about the class either way; an arm's is looked for at the classes a way into it
                // leaves, and named for those it read as the class's line — the same words twice,
                // so the arm's news was dropped as a repeat of the class's (issue #1009).
                // A line held against the lines beside it is named for the finding too, and for the
                // same reason: the search is made at a point of the line, so the place it names is
                // a point a row already stands at — printed, it reads as a row missing where one
                // is written. A rewrite is named for the finding as well: what it is about is two
                // arms of one fork, and the search's words are where it looked for a row.
                // And joined under what the line shows, which leaves out what a search was about
                // where the line is named for the finding.
                case GenerationOutcome.CannotGenerate cannot -> {
                    boolean named = switch (each.finding().about()) {
                        case About.AnArmNoRowGoesThrough _,
                                About.ALineTheRowsDoNotTellFromAnother _,
                                About.ARewriteNoRowTellsApart _,
                                About.ARuleNoRowTakes _,
                                About.ACombinationNoRowMakes _ -> true;
                        default -> false;
                    };
                    for (CameToNothing came : CameToNothing.joinedAsShown(cannot.why(), named
                            ? GeneratedRows::shownUnderItsFinding
                            : GeneratedRows::shownForWhatItIsAbout)) {
                        say(out, saidOf, Owed.by(each.finding()), page,
                                new GeneratedRowsMessage.NoRowForThe(named
                                        ? called(each.finding(), db, module, page, places)
                                                .quoted()
                                        : new ReportMessage.Verbatim(
                                                "`" + came.why().subject() + "`"),
                                        behavior, saidOf(came, page, places)));
                    }
                }
                // Told apart from the one above it in its own words. A strategy that tried and
                // composed nothing and a finding nothing takes are different pieces of news: the
                // first says what the attempt came to, and whether a row can be written at all is
                // its reason's to say; the second says no run of this will offer one until
                // something is written for it.
                // Each of what is missing, for the reason the attempts above are each said: a
                // thing that stands in two places is read at both, and what is missing at one of
                // them is not what is missing at the other.
                case GenerationOutcome.NotSupported none -> none.reasons().forEach(why ->
                        say(out, saidOf, Owed.by(each.finding()), page,
                                openingFor(why, called(each.finding(), db, module, page, places)
                                        .quoted(), behavior, why.told())));
                // Said rather than passed over, because the report counts this coordinate among
                // what is missing and no row is offered for it. Left out, an author reads a gap
                // above and no account of why nothing was written for it; the account is that the
                // line it is a coordinate of is owed one row and has one — written already, or
                // composed at another of the line's positions and offered above.
                case GenerationOutcome.ObligationAlreadySettled _ -> say(out, saidOf,
                        Owed.by(each.finding()), page,
                        new GeneratedRowsMessage.NoRowOfferedAnsweredElsewhere(
                                called(each.finding(), db, module, page, places).quoted(),
                                behavior));
                // Filtered out above, and listed here so that the switch stays exhaustive: an
                // answer added later has to be given words rather than falling silently into
                // whichever arm a default would have put it in.
                case GenerationOutcome.NotApplicable _ -> { }
            }
        }
        List<GenerationReason> stopped = new ArrayList<>(filling.composed().reasons());
        stopped.addAll(filling.boundaries().reasons());
        for (GenerationReason why : stopped) {
            // Through the same set the lines above went through. Two searches of one behavior stop
            // for one reason — nothing built to put a candidate through stops both — and a reader
            // told that twice reads two things having gone wrong.
            switch (why) {
                case GenerationReason.PositionWithheld withheld -> say(out, said, page,
                        new GeneratedRowsMessage.NoRowsOfferedAtAWithheldPosition(
                                String.valueOf(withheld.axis())));
                case GenerationReason.SearchLimit limit -> say(out, said, page,
                        limit.owed() == 1
                                ? new GeneratedRowsMessage.StoppedOneClassOrArmPastTheLimit(
                                        limit.behavior())
                                : new GeneratedRowsMessage.StoppedClassesAndArmsPastTheLimit(
                                        limit.behavior(), limit.owed()));
                // Beside the line above rather than folded into it. That one is a budget an author
                // can raise; this is a walk that was never made, and a reader told the first where
                // the second happened would raise a limit that changes nothing.
                // What was not walked, and not what is missing from the block. A row through an arm
                // behind one of these comes from the way into the arm and is offered above, so a
                // line saying rows were not offered here says a row is owed where one is written.
                case GenerationReason.GroupsNotOffered held -> say(out, said, page,
                        held.groups() == 1
                                ? new GeneratedRowsMessage.OneGroupWasNotLookedIn(held.behavior())
                                : new GeneratedRowsMessage.GroupsWereNotLookedIn(held.groups(),
                                        held.behavior()));
                case GenerationReason.NothingToBuildAgainst none -> say(out, said, page,
                        new GeneratedRowsMessage.StoppedWithNothingToBuildAgainst(
                                none.behavior()));
                case GenerationReason.LinkageFailed failed -> say(out, said, page,
                        new GeneratedRowsMessage.StoppedAsTheClassesWouldNotLink(
                                failed.behavior()));
                // Not a stop. The rows above it are there and are worth writing; what is said is
                // that nothing ran them, so what each is offered for is a reading of the body
                // rather than something anything watched.
                case GenerationReason.RowsNotConfirmed unconfirmed -> say(out, said, page,
                        new GeneratedRowsMessage.RowsOfferedWereNotRun(unconfirmed.behavior()));
                // The reasons it rests on rather than a word of its own. What was not read is a
                // measurement's answer and is already said in those words; saying it again in the
                // generator's would be the same fact under two spellings, read side by side.
                //
                // In the order a document writes them in, which is the order every surface that
                // says these facts writes them in. A block written from the account itself would
                // come out in whatever that iterated in, and a person comparing two generations of
                // one model would be reading the difference between two walks.
                case GenerationReason.RowsNotRead unread -> {
                    for (PublishedIncompleteness because
                            : PublishedIncompleteness.everyOne(unread.because()).written()) {
                        say(out, said, page, new GeneratedRowsMessage.StoppedAsRowsWereNotRead(
                                unread.behavior(), Reasons.told(because.fact(), page)));
                    }
                }
            }
        }
    }

    /**
     * One line, and once. Two gaps can rest on one fact, and a reader owed it is owed it once.
     *
     * <p>Once for what the line says, and never for how a language words it: two lines are one
     * where they say one thing, and two things a language happens to word alike are still two.
     */
    private static void say(StringBuilder out, Set<Message> said, Page page, Message line) {
        if (said.add(line)) {
            out.append("// ").append(page.say(line)).append(System.lineSeparator());
        }
    }

    /** A line about one thing, which is that thing's and is said once for it. */
    private record Said(Owed about, Message line) {}

    /**
     * One line about {@code about}, and once for it. Not once for what it says alone: two things
     * said alike are two, and the second dropped as a repeat of the first is a thing a reader is
     * not told about.
     */
    private static void say(StringBuilder out, Set<Said> said, Owed about, Page page,
                            Message line) {
        if (said.add(new Said(about, line))) {
            out.append("// ").append(page.say(line)).append(System.lineSeparator());
        }
    }

    /**
     * What a point of a body's line is called: the rule that drew the line, said in the words a
     * report says a rule in, and which point of it. The one place a block says a point, whether a
     * finding is about it or a row is handed for it.
     */
    private static Message about(BorderObligationPointAssessment point, Page page,
                                 PublishedRuleHandle.WhereARuleIs places) {
        return new ReportMessage.DeclaredPointOf(point.role().name(),
                RuleHandleProse.said(point.handle(places), page.rendering(), page.language(),
                        null));
    }

    /**
     * What a gap is about, in the words its own finding carries.
     *
     * <p>Read off the value the finding was established with, so that a subject printed here and
     * a subject printed in the report are the same words about the same thing.
     */
    private static Message about(Adequacy.Finding finding, Page page,
                                 PublishedRuleHandle.WhereARuleIs places) {
        return switch (finding.about()) {
            // The point's own words, which is what the edge's own attempt is named by a few lines
            // above ({@code saidOf}). Spelled out here as well, the two vocabularies differed by
            // the role: a point away from the line was written as the value the line is at, which
            // is the one place in reach that such a point is not.
            case About.APointOfABorder(var point) -> about(point, page, places);
            // The same words on what the declaration wrote. Nothing composes a row for one of
            // these yet — the search walks one behavior's inputs and this line is owed once over
            // all of them — so what is printed beside it is that, in its own sentence.
            case About.APointOfADeclaredBorder(var debt) -> new ReportMessage.Verbatim(debt.said());
            // The arm's own short name, which is what the report writes and what the document's
            // `subject` joins on. The finding carries the arm rather than words about it, so that
            // the sentence a diagnostic says in the reader's language and the words written here
            // are two readings of one arm rather than one of them being handed the other's.
            case About.AnArmNoRowGoesThrough(var arm) ->
                    new ReportMessage.Verbatim(ArmVocabulary.label(arm));
            case About.ACaseNoRowAppliesItTo(var _, var missing, var _) ->
                    new ReportMessage.Verbatim(missing.name());
            case About.ACaseNoRowExpects(var _, var missing) ->
                    new ReportMessage.Verbatim(missing.name());
            // The class and the measure it is a class of, which a class name alone does not say:
            // two parameters of one type divide into classes of the same names, and one location is
            // measured at more than one number.
            case About.AClassNoRowIsIn(var missing) ->
                    new GeneratedRowsMessage.TheClassAt(missing.name(), missing.axis().name());
            // The behavior whose decision it is a rule of, which is as far as words about a rule
            // go. What tells one from another is the proposition each of its conditions is keyed
            // on, written the one way round that makes a comparison and its denial one column —
            // and printing that would show an author a comparison they did not write.
            case About.ARuleNoRowTakes(var behavior, var _) ->
                    new GeneratedRowsMessage.ADecisionRuleOf(behavior);
            // Which rewrite, in the words the report writes for it.
            case About.ARewriteNoRowTellsApart(var _, var written, var _, var _, var _) ->
                    RewriteVocabulary.label(written, page);
            // The behavior again, and for the same reason: what the combination is of is written
            // in the terms the account keys on, and a block printing those would hand an author
            // this compiler's spelling of their own body.
            case About.ACombinationNoRowMakes(var combination) ->
                    new GeneratedRowsMessage.ACombinationOfTheDecisionsOf(combination.behavior());
            // The two classes, which is the whole of what one of these is and is something a
            // reader can act on: where a value has to fall at each of two positions.
            case About.ACombinationOfTwoClassesNoRowIsIn(var combination) -> {
                List<Message> each = combination.inOrder().stream()
                        .<Message>map(one -> new GeneratedRowsMessage.TheClassAt(one.classId(),
                                String.valueOf(one.at()))).toList();
                Message said = each.getLast();
                for (int i = each.size() - 2; i >= 0; i--) {
                    said = new GeneratedRowsMessage.TheClassesWith(each.get(i), said);
                }
                yield said;
            }
            // Both lines, which is what a row here would settle between. What is printed beside
            // these words is what the search for such a row came to, and a row that was composed
            // is offered above rather than said here.
            case About.ALineTheRowsDoNotTellFromAnother untold ->
                    new GeneratedRowsMessage.TheLineAgainst(untold.line().border().label(),
                            untold.allowed().label());
            // The position and the total it weighs into, which is the whole of what the weight is
            // of.
            case About.ATiltOfADerivedValueNoRowShows tilt ->
                    new GeneratedRowsMessage.TheWeightOf(String.valueOf(tilt.position()),
                            String.valueOf(tilt.into().left()));
            // Findings row synthesis is not about, which `shown` leaves out and nothing here is
            // asked to name. Listed rather than defaulted so that a shape added later has to be
            // given words here.
            case About.ACaseNothingWasSeenToProduce _,
                    About.ARowAtAnArmAwaitsItsAnswer _, About.AnUnansweredRow _,
                    About.APositionNoLineDivides _, About.APositionThisCouldNotRead _,
                    About.ARuleWithoutALine _, About.ARuleNothingClassified _,
                    About.ARuleThatMayStopARun _,
                    About.AQuestionNothingAnswered _,
                    About.APositionWhoseRulesWereNotReached _,
                    About.APositionReadWiderThanItsRules _ ->
                    throw new IllegalStateException("no row answers this finding: " + finding);
        };
    }

    /**
     * What to print about a combination nothing was written for: what the class said about itself
     * where it said anything, and the category of the answer otherwise.
     *
     * <p>The category is what a reader acts on and the sentence is which case of it this was. A
     * class that recorded why nothing was composed for it knows something the category does not,
     * and printing the category over it loses the one part an author can do anything with.
     *
     * <p><b>And what else was true of the search, after it rather than instead of it.</b> A rule
     * that gave the offer no value is not another way of saying the category — a search stopped at
     * a figure was stopped whether or not a rule beside it gave nothing, and an author acts on
     * both. So the two are joined here, and the one carrier that replaces the category is the one
     * whose whole job is to say which case of it this was.
     */
    private static Message saidOf(Generator.UnresolvedCombination left, Page page,
                                  PublishedRuleHandle.WhereARuleIs places) {
        return beside(left.told().<Message>map(told -> told).orElseGet(() -> why(left.reason())),
                left, page, places);
    }

    /**
     * What a line naming what a search was about is made from, beside what the search met: what
     * it was about, its own sentence or its word ({@link #saidOf(Generator.UnresolvedCombination,
     * Page, PublishedRuleHandle.WhereARuleIs)}), and what else its offer was short of
     * ({@link #beside}). Changed with those and never apart from them.
     */
    static List<Object> shownForWhatItIsAbout(Generator.UnresolvedCombination why) {
        return List.of(why.subject(), sentenceOrWord(why), why.alsoShort());
    }

    /** The same, of a line named for its finding, which does not say what the search was about. */
    static List<Object> shownUnderItsFinding(Generator.UnresolvedCombination why) {
        return List.of(sentenceOrWord(why), why.alsoShort());
    }

    private static Object sentenceOrWord(Generator.UnresolvedCombination why) {
        return why.told().<Object>map(sentence -> sentence).orElse(why.reason());
    }

    /**
     * The same, of a search that says what it met of this compiler's.
     *
     * <p>What was met comes first and the word follows it, the same way round the report opens on
     * a point this compiler stopped at. A reader told first that a figure was reached reads the
     * word as the answer of a search that did not finish; told the word first, they have already
     * made what they were going to make of it — which is a shortfall of this compiler's read as
     * something the model settles.
     */
    private static Message saidOf(CameToNothing came, Page page,
                                  PublishedRuleHandle.WhereARuleIs places) {
        return Reasons.opening(Reasons.met(came), saidOf(came.why(), page, places));
    }

    /**
     * Where a row stops and what looking for one that goes further came to, as said after
     * {@code stops at}.
     *
     * <p>The guard where the author wrote it, and each way past it in the words its search already
     * has ({@link #saidOf(CameToNothing, Page, PublishedRuleHandle.WhereARuleIs)}). Spelled
     * again here, a way this compiler could not compose a row down and a way the rules leave no row
     * down would be one more pair of sentences free to say the same thing; through the one that
     * says every search's word, the first opens on what this compiler fell short at and the second
     * says what the model settles.
     *
     * <p>Each way by where the reading of the body reached it, which is the order the ways are held
     * in. The way a search for them was ordered is a guess about where a row is, and says nothing a
     * reader can find in the source.
     *
     * <p>And for which requirement, where the row answers more than one. The looking was done for
     * one of them, with its classes held, and a reader told only that the row stops would not know
     * whose search said so.
     */
    private static String stoppedShort(RepairShortfall stop, boolean among, Db db, Page page,
                                       PublishedRuleHandle.WhereARuleIs places) {
        String at = Sites.placeOf(db, stop.refused().anchor()).said(page.rendering(), null);
        String guard;
        if (among) {
            List<String> labels = new ArrayList<>();
            stop.soughtFor().forEach(purpose -> labels.addAll(purpose.labels()));
            String said = "`" + labels.getLast() + "`";
            for (int i = labels.size() - 2; i >= 0; i--) {
                said = page.say(new GeneratedRowsMessage.LookingForWith(
                        "`" + labels.get(i) + "`", said));
            }
            guard = page.say(new GeneratedRowsMessage.TheGuardAtLookingFor(at, said));
        } else {
            guard = page.say(new GeneratedRowsMessage.TheGuardAt(at));
        }
        return page.say(switch (stop.came()) {
            case RepairShortfall.AtTheGuard.NoWayPast(List<RepairShortfall.WayPast> ways) -> {
                List<Message> each = new ArrayList<>();
                for (int way = 0; way < ways.size(); way++) {
                    each.add(new GeneratedRowsMessage.WayPastIt(way + 1,
                            wayPast(ways.get(way), page, places)));
                }
                yield new GeneratedRowsMessage.NoRowWasFoundThatGoesPast(guard,
                        Joined.reasons(each));
            }
            // What the reading of the body settles: said as the model's, with nothing about a
            // search, because there was nothing to search for.
            case RepairShortfall.AtTheGuard.NoWayGoesPast _ ->
                    new GeneratedRowsMessage.ItsConditionNeverComesOutThatWay(guard);
            // And this compiler's, said as such: the guard may well let rows past.
            case RepairShortfall.AtTheGuard.WaysNotRead _ ->
                    new GeneratedRowsMessage.TheWaysPastItCouldNotBeRead(guard);
            case RepairShortfall.AtTheGuard.BackAtAGuardLookedPast _ ->
                    new GeneratedRowsMessage.NothingLooksPastOneGuardTwice(guard);
        });
    }

    /** What one way past a guard came to, in the words that kind of answer has. */
    private static Message wayPast(RepairShortfall.WayPast way, Page page,
                                   PublishedRuleHandle.WhereARuleIs places) {
        return switch (way) {
            case RepairShortfall.WayPast.Searched(List<CameToNothing> came) ->
                    saidOf(came, page, places);
            // The figure first, the way every search this compiler stopped is said: what the
            // searches had come to is the answer of looking that did not finish.
            case RepairShortfall.WayPast.CutShort(List<CameToNothing> came,
                                                  Set<CompositionBudget> figures) ->
                    Reasons.opening(Reasons.met(CompositionShortfall.of(figures)),
                            came.isEmpty() ? new GeneratedRowsMessage.NothingWasLookedFor()
                                    : saidOf(came, page, places));
            // Every reason a part gave, in the order the reasons are declared, and the figures that
            // left a part unlooked at first where any did.
            case RepairShortfall.WayPast.NotSearchable(Set<RepairShortfall.Barrier> why,
                                                       Set<CompositionBudget> figures) ->
                    Reasons.opening(Reasons.met(CompositionShortfall.of(figures)),
                            Joined.reasons(why.stream().sorted().map(GeneratedRows::why)
                                    .toList()));
        };
    }

    /** What each of the searches one way was held along came to, each word once, in turn. */
    private static Message saidOf(List<CameToNothing> came, Page page,
                                  PublishedRuleHandle.WhereARuleIs places) {
        return Joined.reasons(came.stream().map(each -> saidOf(each, page, places)).toList());
    }

    /** Why a way past a guard was not looked for, in the words a reader of the block is shown. */
    static Message why(RepairShortfall.Barrier why) {
        return switch (why) {
            case NOTHING_HOLDS_A_ROW_TO_IT -> new GeneratedRowsMessage.NothingHoldsARowToIt();
            case NO_VALUE_CAN_GO_THAT_WAY ->
                    new GeneratedRowsMessage.SoNoRowGoesThisWay(NoValue.goesThatWay());
            case IT_WOULD_REWRITE_A_STATED_VALUE ->
                    new GeneratedRowsMessage.ItWouldRewriteAStatedValue();
            case THE_ROW_ALREADY_DOES_ALL_OF_IT ->
                    new GeneratedRowsMessage.TheRowAlreadyDoesAllOfIt();
        };
    }

    /**
     * {@code category} and what else was true of the search, in one sentence.
     *
     * <p>Here rather than at each surface, because the join is part of what is said: a surface that
     * put the attribution first would say which rule gave nothing before saying what the search
     * came to, and one that wrote its own separator would tell a reader who meets both surfaces
     * that they are reading two different facts.
     */
    static Message beside(Message category, Generator.UnresolvedCombination left, Page page,
                          PublishedRuleHandle.WhereARuleIs places) {
        Message also = alsoShort(left.alsoShort(), page, places);
        return also instanceof ReportMessage.Nothing ? category
                : new ReportMessage.Also(category, also);
    }

    /**
     * What the rules about a position's strings left out of the values offered there, or nothing
     * where they left out none of them.
     *
     * <p>Each rule by the name a report calls rules by, and each reason in the words the document
     * already has for it. Spelled here rather than carried as a sentence: what an author is sent to
     * do turns on which reason it was, and a producer that wrote the words would be a second
     * vocabulary for reasons this one already spells — one that goes stale the first time a reason
     * is added to the other.
     */
    private static Message alsoShort(
            java.util.SequencedMap<TermPath, StringOfferShortfall> shortfall,
            Page page, PublishedRuleHandle.WhereARuleIs places) {
        List<Message> ways = new ArrayList<>();
        for (Map.Entry<TermPath, StringOfferShortfall> at : shortfall.entrySet()) {
            for (StringOfferShortfall.NotOffered each : at.getValue().these()) {
                ways.add(gaveNothing(each, at.getKey(), page, places));
            }
        }
        return Joined.reasons(ways);
    }

    /** One thing that gave the offer no value, said as what it was and what stopped it. */
    private static Message gaveNothing(StringOfferShortfall.NotOffered each, TermPath at,
                                       Page page, PublishedRuleHandle.WhereARuleIs places) {
        // Named by the rule where a rule is what it was about, and never by the position alone: a
        // position carrying two rules about its strings, one of them this compiler cannot read, is
        // one an author fixes by rewriting that one. And never by a rule where what it was about is
        // not one, which is what sends an author to a rule that would have built.
        Message subject = switch (each.of()) {
            case StringOfferShortfall.Subject.ARule it -> new GeneratedRowsMessage.TheRuleAt(
                    RuleHandleProse.said(PublishedRuleHandle.of(
                            new RuleCitation.Named(it.part().rule()), places), page.rendering(),
                            page.language(), null),
                    at.toString());
            case StringOfferShortfall.Subject.WhatTheyLeaveTogether _ ->
                    new GeneratedRowsMessage.WhatTheRulesAboutItLeave(at.toString());
            case StringOfferShortfall.Subject.ComposingAValue _ ->
                    new GeneratedRowsMessage.ComposingAValueFor(at.toString());
        };
        return new GeneratedRowsMessage.GaveNothing(subject, becauseOf(each.why()));
    }

    /**
     * Why it gave nothing, in the words this document has for it.
     *
     * <p>A reading that stopped is said in the vocabulary a document already publishes for such a
     * reading ({@link ReportedReason}), so that a rule reported unread here and the same rule
     * reported unread in the account are one piece of news. What ran out of allowance is not one of
     * those: no rule went unread, and the sentence says what was being done rather than what the
     * rule is.
     */
    static Message becauseOf(StringOfferShortfall.Why why) {
        return switch (why) {
            case StringOfferShortfall.Why.NotRead it -> new GeneratedRowsMessage.GaveNoneAsUnread(
                    AdequacyReport.whyUnread(ReportedReason.of(it.why())));
            case StringOfferShortfall.Why.TooCostly it -> switch (it.stopped()) {
                case ONE_MACHINE -> new GeneratedRowsMessage.GaveNoneForALargerMachine();
                case THE_ANSWER -> new GeneratedRowsMessage.GaveNoneHavingSpentTheComposing();
            };
            case StringOfferShortfall.Why.PatternTooCostly it -> switch (it.stopped()) {
                case ONE_MACHINE -> new GeneratedRowsMessage.GaveNoneForALargerMachine();
                case THE_ANSWER -> new GeneratedRowsMessage.GaveNoneHavingSpentThePattern();
            };
        };
    }

    /**
     * What a reader is told about a search that wrote no row, in this surface's words.
     *
     * <p>Open to the package so that what each word says can be held to what the word means. A
     * sentence that says more than the word does is the way a reader comes to act on something
     * nothing established, and reading it back is the only way to ask whether one does.
     */
    static Message why(Generator.UnresolvedCombination.Reason reason) {
        return switch (reason) {
            case NOTHING_COMPOSES_ONE -> new GeneratedRowsMessage.NothingCouldBuildARepresentative();
            case ALL_CANDIDATES_REJECTED -> new GeneratedRowsMessage.EveryValueTriedWasRefused();
            // The same refusals, and one fewer thing they show. What was offered is not shown to be
            // every value there is, so a reader is told they were refused and not that any value
            // was left untried — whether one was is what nobody knows. Which rule gave none of them
            // follows this, said as the rule it was.
            case NOT_ALL_CANDIDATES_COULD_BE_OFFERED ->
                    new GeneratedRowsMessage.EveryValueTriedWasRefusedOfSome();
            // What is missing is the stand-in and not the row's values, so an author reading this
            // is being told what to write beside the row rather than that no row exists.
            case NOTHING_STANDS_IN_FOR_A_DEPENDENCY ->
                    new GeneratedRowsMessage.NothingCouldAnswerForADependency();
            case A_TABLE_IS_WHAT_THIS_NEEDS -> new GeneratedRowsMessage.ATableIsWhatThisNeeds();
            // As above: one of the two ways a search leaves something untried has a number in it
            // and the other has none, so neither is said as a halt here.
            case THE_SEARCH_LEFT_SOMETHING_UNTRIED ->
                    new GeneratedRowsMessage.TheSearchLeftSomethingUntried();
            case THE_GROUP_WAS_NOT_OFFERED -> new GeneratedRowsMessage.TheGroupWasNotOffered();
            case NO_CERTIFIED_WITNESS -> new GeneratedRowsMessage.NoRowComposedWasSeenReachingIt();
            case THE_WAY_IN_PLACES_AT_NO_CLASS -> new GeneratedRowsMessage.TheWayInPlacesAtNoClass();
            // Nothing was left untried here and nothing is unwritable: the value is in hand and
            // the block is full. What lifts it is the number of rows a block offers, which is not
            // what any of the words above are about.
            case THE_BLOCK_IS_AS_LONG_AS_IT_MAY_BE ->
                    new GeneratedRowsMessage.TheBlockIsAsLongAsItMayBe();
            // What the model settles, said without a word about how this compiler came to know it.
            // Two routes reach here — a walk of the whole of what the rules leave that reached
            // nothing, and a proof that was in hand before anything was walked — and a sentence
            // saying everything was tried is false of the second and tells a reader of the first
            // something they cannot act on either. Nor which part of the model proved it: a type
            // with two values leaves nothing past them with no rule written.
            case NO_VALUE_CAN_STAND_THERE -> NoValue.standsHere();
            case ONE_POSITION_CANNOT_BE_BOTH ->
                    new GeneratedRowsMessage.ItWouldNeedOnePositionToBeTwoThings(
                            NoValue.standsHere());
            case A_CONDITION_NEVER_COMES_OUT_THAT_WAY ->
                    new GeneratedRowsMessage.ItIsPastAConditionThatNeverComesOutSo(
                            NoValue.goesThatWay());
            case NOTHING_TO_BUILD_AGAINST ->
                    new GeneratedRowsMessage.TheModulesClassesWereNotThere();
            case NO_VALUES_WERE_ASKED_FOR -> new GeneratedRowsMessage.ThisBuildComposedNoValues();
            case LINKAGE_FAILED -> new GeneratedRowsMessage.TheGeneratedClassesWouldNotLink();
            case THE_POSITION_WAS_WITHHELD -> new GeneratedRowsMessage.ThePositionWasWithheld();
            case THE_ROWS_WERE_NOT_READ -> new GeneratedRowsMessage.TheRowsWereNotRead();
            case NO_CANDIDATE_WAS_OFFERED -> new GeneratedRowsMessage.NoCandidateWasOffered();
            case NO_READING_OF_THE_LINE_COULD_BE_SEARCHED ->
                    new GeneratedRowsMessage.NoReadingOfTheLineCouldBeSearched();
            // The body's statement and not the model's: nothing proves no input arrives there, and
            // what is known is that the compiler refuses a row that does.
            case EVERY_ROW_THERE_REACHES_AN_UNREACHABLE ->
                    new GeneratedRowsMessage.EveryRowComposedReachesAnUnreachable();
        };
    }


    private GeneratedRows() {}
}
