package souther.compiler.report;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.fmt.Formatter;
import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationReason;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Rows a person completes, printed rather than written.
 *
 * <p>Commented out, every one of them. A generated row is a question — these inputs, and what does the
 * old system answer? — and a row that compiled would be an assertion that nobody made and that the next
 * build would hold the model to. So the block goes out as text to read, paste, answer, and uncomment,
 * and the expected side is left as {@code <?>}, which is not something the grammar accepts and cannot
 * be uncommented by accident.
 *
 * <p>Nothing is written to a file. Where the rows belong is a question with a real answer — the
 * module's own source or an attached {@code examples for} file — and one this does not have to guess
 * at, because a person who can read the block can put it where they want it.
 */
public final class GeneratedRows {

    /** The placeholder an author replaces. Deliberately not a term: uncommenting a row without
     * answering it is a syntax error, not a passing test. */
    private static final String UNANSWERED = "<?>";

    /**
     * The block for a finished compile, for the modules and behaviors the caller asked about.
     *
     * <p>Asked here and not with the rest of a compile's questions, because filling the combinations
     * searches the pair space, and nobody who only wanted the report should pay for that. The rows at
     * the edges cost nothing here: each was built where the boundary was measured, and this reads what
     * that attempt produced.
     *
     * <p>{@code names} is what the caller calls its sources, for the same reason the report beside
     * this block asks for it: a note here is read in the same terminal, and a source id is an
     * identity rather than a name.
     */
    public static String of(Compilation compilation, String module, String behavior,
                            boolean boundaries, SourceNameResolver names) {
        StringBuilder out = new StringBuilder();
        for (String name : compilation.modules()) {
            if (module != null && !module.equals(name)) {
                continue;
            }
            Map<String, Adequacy.Filling> filling =
                    compilation.db().ask(new Adequacy.Generated(name)).value();
            if (filling == null) {
                continue;
            }
            if (behavior != null) {
                Map<String, Adequacy.Filling> only = new LinkedHashMap<>();
                if (filling.containsKey(behavior)) {
                    only.put(behavior, filling.get(behavior));
                }
                filling = only;
            }
            out.append(of(name, filling, WrittenEnsures.of(compilation.db(), name),
                    boundaries, names));
        }
        return out.toString();
    }

    /**
     * The whole block for one module, or an empty string where there is nothing to fill.
     *
     * @param module     the module the rows are about, which an attached file names in its header
     * @param generated  one filling per behavior, keyed the way a report keys them
     * @param ensures    what each behavior has written in its {@code ensures}, in the author's own
     *                   words and keyed as {@code generated} is. Read before this is called and
     *                   handed over: what the source says is not something a renderer works out, and
     *                   a form of this that could be called without it would be a way of dropping it
     * @param boundaries whether to add the rows that sit on an edge nothing has been written at
     * @param names      what the caller calls its sources, for the notes that name one
     */
    public static String of(String module, Map<String, Adequacy.Filling> generated,
                            Map<String, List<String>> ensures,
                            boolean boundaries, SourceNameResolver names) {
        List<Map.Entry<String, Composed>> asked = new ArrayList<>();
        for (Map.Entry<String, Adequacy.Filling> behavior : generated.entrySet()) {
            asked.add(Map.entry(behavior.getKey(),
                    new Composed(behavior.getValue().composed().rows(),
                            boundaries ? behavior.getValue().boundaries().rows() : List.of())));
        }
        // Written once and then read three times — printed, counted, and asked whether there is
        // anything to answer. Counting the candidates instead gives a number about work a reader
        // cannot see, and asking the candidates whether the block holds a hole prints the line
        // telling them to fill one over a block that has none.
        Map<String, List<Offered>> offered = offered(asked);
        int rows = offered.values().stream().mapToInt(List::size).sum();
        StringBuilder out = new StringBuilder();
        if (rows > 0) {
            out.append(String.format(
                    "// generated by `souther examples --generate`: %d %s to fill what nothing covers.%n",
                    rows, rows == 1 ? "row" : "rows"));
            out.append(String.format(
                    "// Replace each `%s` with what the system actually answers, then uncomment.%n",
                    UNANSWERED));
            out.append(commented(stated(blocks(module, offered), ensures)));
        }
        for (Map.Entry<String, Adequacy.Filling> behavior : generated.entrySet()) {
            notes(out, behavior.getKey(), behavior.getValue(), boundaries, names);
        }
        return out.toString();
    }

    /**
     * The findings this block owes a reader a word about.
     *
     * <p>An edge is offered where the caller asked for edges, and everything else is offered either
     * way: a run that did not ask about the lines a model draws still printed the arms and the cases
     * nothing reaches, and what the generator can do about those does not depend on the flag.
     *
     * <p>What an edge is, is read off what the finding is about and not off its kind. A border owes
     * rows at four points and they arrive under two kinds — the two against the line and the two away
     * from it — so a flag written to one of the kinds offered the caller who asked for no edges the
     * other two.
     *
     * <p>A finding row synthesis is not about is left out. This block is rows to write and notes
     * about rows that could not be written; a measure this compiler could not make has no row
     * waiting behind it, and a line here saying nothing offers one would put our own shortfall in
     * a list of the author's work. The report says those findings, which is where they belong.
     */
    private static List<Adequacy.GenerationDisposition> shown(Adequacy.Filling filling,
                                                              boolean boundaries) {
        return filling.generation().stream()
                .filter(each -> !(each.outcome() instanceof GenerationOutcome.NotApplicable))
                .filter(each -> boundaries
                        || !(each.finding().about() instanceof About.APointOfABorder))
                .toList();
    }

    /** A name no answer is written under, standing where the answer goes while the rows are put into
     * the form {@code souther fmt} writes. It is a term and {@link #UNANSWERED} is not, which is the
     * whole reason for the substitution: the formatter parses, and a hole does not parse. */
    private static final String PLACEHOLDER = "unanswered__";

    /**
     * One row as it will be written, and everything it was composed for.
     *
     * <p>A candidate is composed once per thing it is owed for, and the positions that thing does
     * not name hold whatever the row has to hold — so two of them can come out as one row. What is
     * offered is the row: a reader is handed one piece of work rather than the same values twice.
     *
     * <p><b>Every purpose, and not the first.</b> Two purposes converging on one row is a fact
     * about this run, and dropping one of them keeps a name that says the row is about one thing
     * while it answers two — which is what a name for the first arrival was. Joining them into one
     * name is the other way of being wrong: {@code "a x b"} reads as one thing owed at two
     * positions at once, which is the shape this whole block was written against.
     *
     * <p>So one purpose is a name and several are a note apiece over a row with none. The language
     * lets a row be written without a name and an author names it when they answer it; what it is
     * for is said in words above it, once per thing.
     *
     * @param inputs   the row's values, in the form they are written in
     * @param purposes what it was composed for, in the order the things were taken
     */
    private record Offered(String inputs, List<String> purposes) {

        Offered {
            purposes = List.copyOf(purposes);
        }

        /** The same, and one more thing it turned out to answer. Kept in order and without
         *  repeats: two purposes with one name are one thing said twice. */
        Offered and(String purpose) {
            if (purpose == null || purposes.contains(purpose)) {
                return this;
            }
            List<String> both = new ArrayList<>(purposes);
            both.add(purpose);
            return new Offered(inputs, both);
        }

        /** The row as it is written: named where one thing names it, and not otherwise. What a
         *  row with several is for is said over it ({@link #blocks}) rather than in it — the
         *  formatter parses what it is handed, and prose is not a row. */
        String written() {
            return purposes.size() == 1
                    ? "    | \"" + purposes.get(0) + "\" : (" + inputs + ") -> " + PLACEHOLDER
                    : "    | (" + inputs + ") -> " + PLACEHOLDER;
        }

        /** What to say over the row, which is nothing where its name already says it. */
        List<String> saidOver() {
            return purposes.size() == 1 ? List.of() : purposes;
        }
    }

    /** What one behavior's rows were composed for: the cells of its partition, and the lines a rule
     * draws. Kept apart because a row's name comes from what it was composed for. */
    private record Composed(List<Generator.GeneratedRow> cells, List<Generator.GeneratedRow> lines) {}

    /**
     * The candidates as rows, one per row rather than one per obligation.
     *
     * <p>Grouped on what is written, which is what a reader would be pasting twice. Not on the values
     * themselves: two rows of one behavior meaning the same thing and spelt differently stay two rows,
     * each naming its own obligation, and that is the direction to be wrong in. A grouping on values
     * would need an identity for them that nothing here has — a fixture carries the position it was
     * parsed at and the path it was constructed through — and the row a person reads is the row.
     *
     * <p>A row is named for what it was composed for and not for everything it turned out to settle.
     * The two are different questions: which row this is, and what this run of the generator is
     * handing it. The second changes with the rest of the model — a row written elsewhere can meet a
     * line this row also sits on, and the line stops being offered — and a name that moved with it
     * would be a name for the state of the generation rather than for the row.
     *
     * <p>A cell can name a row: two cells never compose one row, since a candidate's values follow
     * from the classes it was composed for, so the cell a row is named by is the row's own and is
     * there whatever else this run offers. A line cannot. Lines coincide — each probe fills the
     * positions its own edge does not name from the bottom of their domains, so two minimum edges
     * compose one row — and which of them is offered is exactly what changes when something else is
     * written: a row meeting one of the two leaves the other, and a row named for whichever line
     * happened to be offered would be renamed by an edit that did not touch it. That is the same
     * fault as naming a row for everything it settles, with the joining written as a choice.
     *
     * <p>So a row composed only for lines is offered without a name. Nothing here can name it from
     * one thing, and the language lets a row be written without one — an unnamed row cannot be
     * addressed from outside, which is exactly the state of a row nobody has named yet. The author
     * names it when they answer it. What a row sits on is in the report, where what this run owes is
     * said.
     */
    private static Map<String, List<Offered>> offered(List<Map.Entry<String, Composed>> asked) {
        // One block per behavior, however many kinds of row it holds. Rows of one behavior written
        // under two headings are legal and read as two lists of something, which they are not.
        Map<String, Map<String, Offered>> byBehavior = new LinkedHashMap<>();
        for (Map.Entry<String, Composed> behavior : asked) {
            Map<String, Offered> here =
                    byBehavior.computeIfAbsent(behavior.getKey(), _ -> new LinkedHashMap<>());
            for (Generator.GeneratedRow row : behavior.getValue().cells()) {
                String inputs = String.join(", ", textsOf(row.inputs()));
                here.merge(inputs, new Offered(inputs, List.of(row.description())),
                        (had, _) -> had.and(row.description()));
            }
            // A row composed for an edge is offered without one. The points of a border coincide —
            // each probe fills the positions its own edge does not name from the bottom of their
            // domains, so two minimum edges compose one row — and which of them is offered is
            // exactly what changes when something else is written.
            for (Generator.GeneratedRow row : behavior.getValue().lines()) {
                String inputs = String.join(", ", textsOf(row.inputs()));
                here.putIfAbsent(inputs, new Offered(inputs, List.of()));
            }
        }
        Map<String, List<Offered>> out = new LinkedHashMap<>();
        byBehavior.forEach((behavior, rows) -> out.put(behavior, List.copyOf(rows.values())));
        return out;
    }

    /**
     * The rows as source, in the form the formatter writes them.
     *
     * <p>Formatted rather than printed straight, because these lines are meant to be pasted into a
     * file that {@code souther fmt} then runs over. A block that came out in a shape the formatter
     * would change turns a paste into a diff on the next commit.
     */
    private static String blocks(String module, Map<String, List<Offered>> offered) {
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
        return fills(formatted.replaceFirst("^examples for \\S+\\R+", "")
                .replace(PLACEHOLDER, UNANSWERED), offered);
    }

    /**
     * What each row with more than one thing to its name is for, said over it.
     *
     * <p>Put in after the formatter has run, for the reason the {@code ensures} headings are: what
     * {@link #blocks} hands the formatter is source, and a line of prose is not a row. Written into
     * the source instead, the formatter would refuse the whole block and it would go out in
     * whatever shape it happened to be built in.
     *
     * <p>Matched by position rather than by reading the line. The rows go in in one order and come
     * out in it, and a row the formatter wrapped is still one row — its continuations are indented
     * past the {@code |} that starts it, so what starts a row is what a row starts with.
     */
    private static String fills(String rows, Map<String, List<Offered>> offered) {
        List<Offered> inOrder = new ArrayList<>();
        offered.values().forEach(inOrder::addAll);
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (String line : rows.lines().toList()) {
            if (line.startsWith(ROW) && at < inOrder.size()) {
                for (String each : inOrder.get(at++).saidOver()) {
                    out.append("fills ").append(each).append(System.lineSeparator());
                }
            }
            out.append(line).append(System.lineSeparator());
        }
        return out.toString();
    }

    /** How a row starts, which is how one is told from the lines a wrapped one continues on: those
     *  are indented past it. */
    private static final String ROW = "    | ";

    /** What the heading over a behavior's clauses says. A source-level fact and not a reading of one:
     * these are the words the author put in the declaration, quoted here whether or not the checker
     * could make a rule of them, so what is claimed is that they are written and nothing further. */
    private static final String WRITTEN_FOR = "`ensures` written for `%s`:%n";

    /**
     * The clauses each behavior carries, put over the rows they are about.
     *
     * <p>Over the rows and not beside each one. A clause is written on the behavior, so it says the
     * same thing about every row of it, and a copy per row would be the same words as many times as
     * the generator happened to offer questions.
     *
     * <p>Put in after {@link #blocks} and not inside it, because these lines are not rows. What that
     * builds is source, written so that {@code souther fmt} would leave it alone; a heading is prose
     * the whole block is commented behind, and the formatter parses what it is handed.
     */
    private static String stated(String source, Map<String, List<String>> ensures) {
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
                out.append(String.format(WRITTEN_FOR, behavior));
                for (String clause : clauses) {
                    for (String each : clause.lines().toList()) {
                        out.append("    ").append(each).append(System.lineSeparator());
                    }
                }
                out.append(System.lineSeparator());
            }
            out.append(line).append(System.lineSeparator());
        }
        return out.toString();
    }

    private static String commented(String source) {
        StringBuilder out = new StringBuilder();
        for (String line : source.lines().toList()) {
            out.append(line.isEmpty() ? "//" : "// " + line).append(System.lineSeparator());
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
                              boolean boundaries, SourceNameResolver names) {
        Set<String> said = new LinkedHashSet<>();
        List<Generator.UnresolvedCombination> left =
                new ArrayList<>(filling.composed().unresolved());
        if (boundaries) {
            left.addAll(filling.boundaries().unresolved());
        }
        for (Generator.UnresolvedCombination each : left) {
            say(out, said, String.format("// no row for `%s` in `%s`: %s%n",
                    each.subject(), behavior, saidOf(each)));
        }
        // Every finding a row could answer, and not only the ones a strategy took. One printed in
        // the report and left out of this block is one an author is told nothing about, while the
        // rows above it read as though they filled everything.
        for (Adequacy.GenerationDisposition each : shown(filling, boundaries)) {
            switch (each.outcome()) {
                case GenerationOutcome.Generated _ -> { }
                case GenerationOutcome.CannotGenerate cannot -> say(out, said,
                        String.format("// no row for `%s` in `%s`: %s%n", cannot.why().subject(),
                                behavior, saidOf(cannot.why())));
                // Told apart from the one above it in its own words. A strategy that tried and
                // composed nothing and a finding nothing takes are different pieces of news: the
                // first says a row may still be writable by hand, the second says no run of this
                // will offer one until something is written for it.
                case GenerationOutcome.NotSupported none -> say(out, said,
                        String.format("// nothing offers a row for `%s` in `%s`: %s%n",
                                about(each.finding()), behavior, none.reason().said()));
                // Filtered out above, and listed here so that the switch stays exhaustive: a
                // fourth answer added later has to be given words rather than falling silently
                // into whichever arm a default would have put it in.
                case GenerationOutcome.NotApplicable _ -> { }
            }
        }
        List<GenerationReason> stopped = new ArrayList<>(filling.composed().reasons());
        if (boundaries) {
            stopped.addAll(filling.boundaries().reasons());
        }
        for (GenerationReason why : stopped) {
            // Through the same set the lines above went through. Two searches of one behavior stop
            // for one reason — nothing built to put a candidate through stops both — and a reader
            // told that twice reads two things having gone wrong.
            lines(out, said, switch (why) {
                case GenerationReason.PositionWithheld withheld -> String.format(
                        "// no rows offered at `%s`: a row's value there could not be read, so a"
                                + " row written for it may be one that is already here%n",
                        withheld.axis());
                case GenerationReason.SearchLimit limit -> String.format(
                        "// generation stopped for `%s`: %d %s past the row limit%n",
                        limit.behavior(), limit.combinations(),
                        limit.combinations() == 1 ? "combination" : "combinations");
                case GenerationReason.NothingToBuildAgainst none -> String.format(
                        "// generation stopped for `%s`: there was nothing to build a candidate"
                                + " against%n", none.behavior());
                case GenerationReason.LinkageFailed failed -> String.format(
                        "// generation stopped for `%s`: the generated classes would not link, so"
                                + " the decoders a candidate is built through were out of reach%n",
                        failed.behavior());
                // Not a stop. The rows above it are there and are worth writing; what is said is
                // that nothing ran them, so what each is offered for is a reading of the body
                // rather than something anything watched.
                case GenerationReason.RowsNotConfirmed unconfirmed -> String.format(
                        "// rows offered for `%s` were not run, so which combination each reaches"
                                + " is read off the body rather than observed%n",
                        unconfirmed.behavior());
                // The reasons it rests on rather than a word of its own. What was not read is a
                // measurement's answer and is already said in those words; saying it again in the
                // generator's would be the same fact under two spellings, read side by side.
                case GenerationReason.RowsNotRead unread -> {
                    StringBuilder lines = new StringBuilder();
                    for (Incompleteness because : unread.because()) {
                        lines.append(String.format("// generation stopped for `%s`: %s%n",
                                unread.behavior(), Reasons.said(because, names)));
                    }
                    yield lines.toString();
                }
            });
        }
    }

    /** Each line of what a reason came to, and each of them once. */
    private static void lines(StringBuilder out, Set<String> said, String written) {
        for (String line : written.lines().toList()) {
            say(out, said, line + System.lineSeparator());
        }
    }

    /** One line, and once. Two gaps can rest on one fact, and a reader owed it is owed it once. */
    private static void say(StringBuilder out, Set<String> said, String line) {
        if (said.add(line)) {
            out.append(line);
        }
    }

    /**
     * What a gap is about, in the words its own finding carries.
     *
     * <p>Read off the value the finding was established with, so that a subject printed here and
     * a subject printed in the report are the same words about the same thing.
     */
    private static String about(Adequacy.Finding finding) {
        return switch (finding.about()) {
            // The point's own words, which is what the edge's own attempt is named by a few lines
            // above ({@code saidOf}). Spelled out here as well, the two vocabularies differed by
            // the role: a point away from the line was written as the value the line is at, which
            // is the one place in reach that such a point is not.
            case About.APointOfABorder(var point) -> point.said();
            // The arm's own short name, which is what the report writes and what the document's
            // `subject` joins on. The finding carries the arm rather than words about it, so that
            // the sentence a diagnostic says in the reader's language and the words written here
            // are two readings of one arm rather than one of them being handed the other's.
            case About.AnArmNoRowGoesThrough(var arm) -> ArmVocabulary.label(arm);
            case About.ACaseNoRowAppliesItTo(var input, var missing) -> missing.name();
            case About.ACaseNoRowExpects(var missing) -> missing.name();
            // The class and the position it is a class of, which a class name alone does not say:
            // two parameters of one type divide into classes of the same names.
            case About.AClassNoRowIsIn(var missing) ->
                    missing.name() + " at " + missing.axis().path();
            // Findings row synthesis is not about, which `shown` leaves out and nothing here is
            // asked to name. Listed rather than defaulted so that a shape added later has to be
            // given words here.
            case About.ACaseNothingWasSeenToProduce _,
                    About.APositionNoLineDivides _, About.APositionThisCouldNotRead _,
                    About.ARuleThisCouldNotRead _,
                    About.AQuestionNothingAnswered _,
                    About.APositionWhoseRulesWereNotReached _,
                    About.APositionReadWiderThanItsRules _,
                    About.APositionPastTheAxisLimit _ ->
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
     */
    private static String saidOf(Generator.UnresolvedCombination left) {
        return left.said().orElseGet(() -> why(left.reason()));
    }

    private static String why(Generator.UnresolvedCombination.Reason reason) {
        return switch (reason) {
            case NOTHING_COMPOSES_ONE ->
                    "nothing here could build a representative for it, which does not make one"
                            + " unwritable";
            case ALL_CANDIDATES_REJECTED ->
                    "every value tried was refused at construction, which does not make the"
                            + " combination impossible";
            case SEARCH_LIMIT -> "the search stopped before reaching it";
            case NO_CERTIFIED_WITNESS ->
                    "no row composed for it was seen reaching it, which does not make the"
                            + " combination unreachable";
            case THE_RULES_LEAVE_NOTHING_THERE ->
                    "the rules leave no value here, and every combination they do leave was tried";
            case NOTHING_TO_BUILD_AGAINST ->
                    "the module's classes were not there to build a candidate against";
            case LINKAGE_FAILED ->
                    "the generated classes would not link, so the decoders a candidate is built"
                            + " through were out of reach";
            case THE_POSITION_WAS_WITHHELD ->
                    "a row's value at that position could not be read, so no class of it was looked"
                            + " for — one written for it may be one that is already here";
            case THE_ROWS_WERE_NOT_READ ->
                    "the rows were not read, so nothing was looked for; what stopped them being"
                            + " read is said above";
            case NO_REASON_RECORDED ->
                    "the search that takes this class left no reason, which is this compiler failing"
                            + " to say rather than anything established about the class";
        };
    }

    private static List<String> textsOf(List<FixtureTemplate> inputs) {
        return inputs.stream().map(FixtureTemplate::text).toList();
    }

    private GeneratedRows() {}
}
