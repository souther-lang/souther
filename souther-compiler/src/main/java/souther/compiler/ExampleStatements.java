package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceRef;
import souther.compiler.evaluate.DepthLimitExceeded;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;
import souther.compiler.observe.FailurePhase;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Reads the statements a module writes about one of its behaviors, and reports where two of them
 * answer differently.
 *
 * <p>Nothing is applied. A row of an {@code example} says what a behavior will owe for an input; a
 * {@code fake} table and a {@code with} say what stands in for it while some *other* behavior's row
 * runs. Those are two people writing down an answer to the same question, and where the answers
 * differ the model contradicts itself whichever one is right — which is readable from the text
 * alone, with no behavior run and no result to compare against (#306).
 *
 * <p>Apart from {@link ExampleVerifier} because they answer different questions for different keys
 * and neither reads the other's state. What they share is underneath both: {@link FixtureReader}
 * reads a written fixture as the value it states, and each of these says for itself what a fixture
 * that will not build, or will not finish, means where it is.
 *
 * <p>A written {@code fake} table is built here too, because it is written. A table stands in for a
 * behavior and is read against the rows recorded for it, and a module can write one that neither of
 * those reaches — nothing depends on the faked behavior and no row records what it owes. It still
 * states what it states, and what is wrong with it is wrong wherever it is read from.
 *
 * <p>{@link Standins} is the one place a fake's table is built and the one rule by which a row of it
 * answers ({@link Standins#answering}). Both are shared with the proxy {@link ExampleVerifier}
 * installs while a row runs, deliberately: a second reading of one table is the thing <em>E1919</em>
 * exists to catch, so there must not be a second reading to drift.
 */
public final class ExampleStatements {

    private final Ast.Module module;
    private final Symbols symbols;
    private final Map<String, Sig> sigs;
    private final MemoryClassLoader loader;
    /** The values a statement may name: this module's own, and the ones its imports bring in. */
    private final Map<String, Ast.FnDef> values;
    /** A reader kept for showing a value that was already built ({@link #shown}), which is the one
     * thing a reader does that reads none of its own state: nothing is expanded, no binding is put in
     * force and no helper is run, so there is no reading here to isolate. What it is for is the
     * module's encoders and its loader. Every actual reading gets {@link #newFixtureReader()}. */
    private final FixtureReader rendering;
    /** What one written statement gets to be read within ({@link #within}). Carried rather than
     * looked up, so two compiles in one JVM need not agree on it. */
    private final Deadline deadline;
    /** What one reading is allowed. A statement is read by running the helpers its fixtures apply, so
     * it is held to the same counted budget a row is: what is read is decided by what the statements
     * say, not by how fast the host reading them is. */
    private final EvaluationPolicy policy;

    private ExampleStatements(Ast.Module module, Symbols symbols, Map<String, Sig> sigs,
                              MemoryClassLoader loader, Map<String, Ast.FnDef> values,
                              Deadline deadline, EvaluationPolicy policy) {
        this.module = module;
        this.symbols = symbols;
        this.sigs = sigs;
        this.loader = loader;
        this.values = values;
        this.deadline = deadline;
        this.policy = policy;
        this.rendering = new FixtureReader(module, symbols, values, loader);
    }

    /**
     * A reader for one written statement, held for as long as reading it lasts.
     *
     * <p>Never shared between two of them. Building a fixture runs the helpers it applies (ADR-0077)
     * and a {@code partial} one may not stop, so a reading that runs out of its budget is asked to
     * stop and cannot be made to — and what it goes on writing to is this.
     */
    private FixtureReader newFixtureReader() {
        return new FixtureReader(module, symbols, values, loader);
    }

    private Set<TypeName> outCases(Type out) {
        return TypeOps.outputCases(out, symbols);
    }

    // --- two statements about one behavior -----------------------------------------------------

    /**
     * Every input for which two of this module's written statements about one behavior answer
     * differently.
     *
     * <p>{@code module} is the whole module — every row and every fake, whichever source wrote it. A
     * fake and the rows it disagrees with need not be in one file, so neither side can be found from
     * one source's share of them. {@code exampleOrigins} and {@code fakeOrigins} say which source each
     * came from, in the order {@code module} holds them.
     *
     * <p>No behavior is applied. What a fake answers for an input is decided by the rule the fake
     * itself dispatches with ({@link Standins#answering}) — the same rule, not a second reading of it — and
     * the two answers are compared as the written values they are built into.
     */
    public static Readings disagreements(Ast.Module module, Symbols symbols,
                                         Map<String, Sig> sigs, Map<String, byte[]> classes,
                                         ClassLoader parent, Map<String, Ast.FnDef> values,
                                         List<String> exampleOrigins,
                                         List<String> fakeOrigins, Deadline deadline,
                                         EvaluationPolicy policy) {
        if (module.examples().isEmpty()
                || exampleOrigins.size() != module.examples().size()
                || fakeOrigins.size() != module.fakes().size()) {
            return Readings.NONE;
        }
        // Which behaviors have both a stand-in and rows of their own, read off the text. Two written
        // statements are what this is about, and where there are not two there is nothing to build:
        // a module whose faked behaviors are exampled nowhere — which is most of them, since a fake is
        // written so that some *other* behavior's rows can run — is settled here, before a class is
        // loaded or a worker is started.
        Set<String> contested = contested(module, sigs);
        if (contested.isEmpty()) {
            return Readings.NONE;
        }
        ExampleStatements v = new ExampleStatements(module, symbols, sigs,
                new MemoryClassLoader(classes, parent), values, deadline, policy);
        return v.collectDisagreements(exampleOrigins, fakeOrigins, contested);
    }

    /**
     * What building this module's fake tables says about the ones {@code sourceId} wrote, each built
     * once.
     *
     * <p>Because they are written, not because something reads them. A table is built to stand in for
     * a behavior (where {@link ExampleVerifier} resolves it for a row) and to be read against the rows
     * recorded for it ({@link #againstFake}), and a module can write one that neither of those reaches:
     * nothing in it depends
     * on the faked behavior, and no row records what that behavior owes. The table still states what
     * it states, and what is wrong with it is wrong wherever it is read from.
     *
     * <p>The one place it is said, so a build and a row cannot come to two answers about one table.
     * A row that applies a fake it could not build says nothing about the table any more — it does not
     * run, and the error at the fake is what the compile fails on — which also ends the same table
     * being reported once per row that reaches it.
     *
     * <p>The tables that answer, which is what the other two readers build: the first one written for
     * a dependency. A second written for the same name stands in for nothing and is read by nobody,
     * so building it here would hold a table to something no reader of it would ever ask.
     *
     * <p>{@code fakeOrigins} says which source wrote each of {@code module.fakes()}, in that order —
     * every fake, since which one answers for a dependency is a fact about the module and not about
     * one of its files. Where it does not line up with them, every table that answers is built here:
     * a report in the wrong file is a report, and the reason to know the file is to place it, while
     * nothing else would say what is wrong with the table at all.
     */
    public static List<Diagnostic> fakeTables(Ast.Module module, Symbols symbols,
                                              Map<String, Sig> sigs, Map<String, byte[]> classes,
                                              ClassLoader parent, Map<String, Ast.FnDef> values,
                                              List<String> fakeOrigins, String sourceId,
                                              Deadline deadline, EvaluationPolicy policy) {
        if (module.fakes().isEmpty()) {
            return List.of();
        }
        boolean placed = fakeOrigins.size() == module.fakes().size();
        ExampleStatements v = new ExampleStatements(module, symbols, sigs,
                new MemoryClassLoader(classes, parent), values, deadline, policy);
        List<Diagnostic> said = new ArrayList<>();
        Set<String> answering = new LinkedHashSet<>();
        for (int i = 0; i < module.fakes().size(); i++) {
            Ast.Fake fk = module.fakes().get(i);
            if (!answering.add(fk.target())) {
                continue;   // a second table for one dependency answers nothing, here as anywhere
            }
            if (placed && !fakeOrigins.get(i).equals(sourceId)) {
                continue;   // written in another source, and built by that source's own reading
            }
            Sig sig = sigs.get(fk.target());
            if (sig == null) {
                continue;   // a fake for no behavior of this module; its target is its own question
            }
            // Within a budget of its own, for the reason a row and a reading each have one: a row of
            // the table applies helpers, and a `partial` one may not stop. Nothing before this change
            // built the table of a fake nothing reads, so this is the first thing that would run it.
            Read<List<Diagnostic>> read = v.within(reader -> {
                List<Diagnostic> wrong = new ArrayList<>();
                standins(reader, fk, sig.ins(), sig.out(), wrong);
                return wrong;
            }, new Deadline.Work.Table(fk.target(), sourceId, fk.pos()));
            switch (read) {
                case Read.Got(List<Diagnostic> wrong) -> said.addAll(wrong);
                case Read.Overspent(FailurePhase which, long limit) ->
                        said.add(unreadableFake(fk, Unread.overspending(which, limit)));
                case Read.StackRanOut(int depthLimit) ->
                        said.add(unreadableFake(fk, new Unread.StackRanOut(depthLimit)));
                case Read.Unanswered(long ranOutOf) ->
                        said.add(unreadableFake(fk, new Unread.DidNotAnswer(ranOutOf)));
                // Not about this fake: the runtime is `provided`, so a host without it builds no value
                // at all and every fake in every module would say the same thing. Where the rows are
                // evaluated that is recorded once, as an incompleteness.
                case Read.RuntimeAbsent() -> { }
            }
        }
        return List.copyOf(said);
    }

    /**
     * What one reading came to: the statement, or the reason there is no statement.
     *
     * <p>The reason is answered rather than dropped because the two reasons are held against
     * different things. A statement that did not finish is about this module, and where nothing else
     * builds what it was reading it is this reading's to say; a host with no runtime is about the
     * host, and says the same thing about every fake and every row in every module compiled on it.
     * A reader that got only "nothing was read" would have to pick one of those, and each caller
     * would pick for itself.
     */
    private sealed interface Read<T> {

        /** What the reading answered. Null where the statement is written in a form that states
         * nothing — an input that will not build, an expectation that cannot be read. */
        record Got<T>(T value) implements Read<T> {}

        /** The reading spent what the policy allows, and which budget it spent: the statements say
         * something this compiler will not read all of, and it says so the same way on every host. */
        record Overspent<T>(FailurePhase which, long limit) implements Read<T> {}

        /** The stack ran out before the counted depth limit was reached, and the limit it did not
         * reach. Not a statement about the table either: how many frames a stack holds is decided by
         * how large they are. */
        record StackRanOut<T>(int depthLimit) implements Read<T> {}

        /** The reading stopped answering, and the wait it was held to: what a report has to name is
         * what the wait actually was, not what a second reader of the setting makes of it later.
         *
         * <p>Not a statement about the model. Whatever did not come back was not counted — code from
         * a jar this compile did not generate, or the compiler itself — so nothing here can say the
         * statements are at fault. */
        record Unanswered<T>(long budgetMs) implements Read<T> {}

        /** This host has no runtime to build a value against. */
        record RuntimeAbsent<T>() implements Read<T> {}

        /** What was read, or null — for a caller that has nothing of its own to say about why
         * there is nothing. Both reasons come out the same here on purpose: the reading that did
         * not happen is reported by whoever else reads the same statement. */
        default T orNull() {
            return this instanceof Got(T value) ? value : null;
        }
    }

    /**
     * One statement, read within its own share of the budget.
     *
     * <p>Per statement rather than per module. Building a fixture runs the helpers it applies
     * (ADR-0077), and a `partial` one may not stop — so a budget covering the whole reading is one a
     * single slow row can spend, and spending it would drop every other statement's reading with it:
     * a plain contradiction elsewhere in the module would go unsaid because of a row it has nothing
     * to do with. It is what {@link #checkRow} already does for a row it evaluates, and this reads
     * strictly fewer statements than that evaluates rows.
     *
     * <p>What did not finish states nothing. Who says so is the caller's, and differs: a row and a
     * {@code with} written on one are evaluated elsewhere and report it there (E1910), while a fake
     * table is built here and, where no row depends on the behavior it stands in for, nowhere else.
     */
    private <T> Read<T> within(java.util.function.Function<FixtureReader, T> read,
                               Deadline.Work what) {
        // On a reader of its own, and that is all a reading needs to be given: a worker that runs out
        // of budget is asked to stop and cannot be made to — a fixture reaches no interrupt point — so
        // it may still be inside `expandedValue`, holding a binding or a half-walked expansion. What a
        // late worker can still write to is that reader, and the statement after it gets another.
        FixtureReader reader = newFixtureReader();
        switch (deadline.given(what, () -> counted(() -> read.apply(reader)))) {
            case Deadline.Outcome.Finished(T value) -> {
                return new Read.Got<>(value);
            }
            case Deadline.Outcome.Overran(Runnable abandon) -> {
                // Nothing here was going to read how far it got, so it is given up on at once.
                abandon.run();
                return new Read.Unanswered<>(deadline.budgetMs());
            }
            case Deadline.Outcome.Threw(Throwable cause) -> {
                // The reading spent what the policy allows. That is an answer about the statements —
                // the same one on every host — and is told apart from a reading that stopped answering,
                // which is an answer about the host.
                if (cause instanceof StepLimitExceeded) {
                    return new Read.Overspent<>(FailurePhase.STEP_LIMIT, policy.stepLimit());
                }
                if (cause instanceof DepthLimitExceeded) {
                    return new Read.Overspent<>(FailurePhase.DEPTH_LIMIT,
                            policy.recursionDepthLimit());
                }
                // The stack ran out. Said here for the reason the two above are: everything the
                // worker threw arrives at this one place, so classifying anywhere else leaves the
                // paths that do not go through that place unclassified — and an Error rethrown from
                // here is a compiler failure rather than a report about the statement.
                if (cause instanceof StackOverflowError || cause instanceof StackExhaustedException) {
                    // Both forms of the same thing. A stack that runs out inside a helper crosses a
                    // reflection boundary on the way here and arrives named; one that runs out
                    // anywhere else arrives raw. Recognising only the raw one left the named one to
                    // the rethrow below, where a `RuntimeException` leaves the compilation as a
                    // failure of the compiler rather than as a report about the table.
                    return new Read.StackRanOut<>(policy.recursionDepthLimit());
                }
                // One thing ends a reading without the model or this code being at fault: a host with
                // no runtime to build a value against, since the runtime is `provided` (as it is for
                // CTFE).
                if (runtimeAbsent(cause)) {
                    return new Read.RuntimeAbsent<>();
                }
                // Anything else is this code being wrong. An empty reading says the statements agree,
                // so answering with one would leave a broken compiler reporting every model
                // consistent, and only a test that reached the broken shape would ever say otherwise.
                if (cause instanceof RuntimeException runtime) {
                    throw runtime;
                }
                if (cause instanceof Error error) {
                    throw error;
                }
                throw new IllegalStateException(cause);
            }
        }
    }

    /**
     * {@code read}, run with this reading's budget counting on the thread it runs on.
     *
     * <p>Started here rather than around the whole reading, because a budget covering every statement
     * is one a single statement can spend — and spending it would drop the reading of every other one
     * with it, so a plain contradiction elsewhere in the module would go unsaid because of a fixture
     * it has nothing to do with. It is the same reason each statement gets its own deadline.
     */
    private <T> T counted(java.util.function.Supplier<T> read) {
        EvaluationContext.begin(policy.stepLimit(), policy.recursionDepthLimit());
        try {
            return read.get();
        } finally {
            EvaluationContext.end();
        }
    }

    /**
     * Whether {@code cause} is this host having no runtime rather than anything being wrong.
     *
     * <p>The runtime is {@code provided}, so a build that compiles Souther without it on the class
     * path can generate the classes and not load them. That is the one {@link LinkageError} that says
     * nothing about the model or about this code — the rest of the family says a class was generated
     * or loaded wrong ({@code VerifyError}, {@code ClassFormatError}, {@code NoSuchMethodError}), and
     * reading those as "no runtime" would let a broken back end report every model consistent.
     */
    private static boolean runtimeAbsent(Throwable cause) {
        return cause instanceof NoClassDefFoundError missing
                && missing.getMessage() != null
                && missing.getMessage().replace('/', '.').startsWith("souther.runtime.");
    }

    /** The behaviors this module both stands in for — the target of a {@code fake}, the dependency a
     * {@code with} that takes no input answers for ({@link #againstWiths}) — and records rows of. */
    private static Set<String> contested(Ast.Module module, Map<String, Sig> sigs) {
        Set<String> stoodIn = new LinkedHashSet<>();
        for (Ast.Fake fk : module.fakes()) {
            stoodIn.add(fk.target());
        }
        for (Ast.Example ex : module.examples()) {
            for (Ast.ExampleRow row : ex.rows()) {
                for (Ast.With w : row.withs()) {
                    Sig depSig = sigs.get(w.dep());
                    if (depSig != null && depSig.inputTypes().isEmpty()) {
                        stoodIn.add(w.dep());
                    }
                }
            }
        }
        Set<String> both = new LinkedHashSet<>();
        for (Ast.Example ex : module.examples()) {
            if (stoodIn.contains(ex.target())) {
                both.add(ex.target());
            }
        }
        return both;
    }

    /** One recorded row, read as far as it can be without running it. What it says is left as written
     * — rendering it builds the fixture a second time, and only a row that turns out to disagree is
     * ever shown. */
    private record RecordedRow(SourceRef at, Ast.Expr expected, Object[] arguments, Answered answer) {}

    private Readings collectDisagreements(List<String> exampleOrigins,
                                          List<String> fakeOrigins, Set<String> contested) {
        Map<String, List<RecordedRow>> recorded = new LinkedHashMap<>();
        for (int i = 0; i < module.examples().size(); i++) {
            Ast.Example ex = module.examples().get(i);
            if (contested.contains(ex.target())) {
                readRecorded(ex, exampleOrigins.get(i), recorded);
            }
        }
        if (recorded.isEmpty()) {
            return Readings.NONE;
        }
        List<Disagreement> found = new ArrayList<>();
        List<UnreadFake> timedOut = new ArrayList<>();
        // The first table for a dependency is the one that answers, as it is for the row that runs
        // against it; a second
        // one written for the same name never stands in for anything, so it states nothing to
        // disagree with. What that second table is, is its own question.
        Set<String> answering = new LinkedHashSet<>();
        for (int j = 0; j < module.fakes().size(); j++) {
            Ast.Fake fk = module.fakes().get(j);
            if (answering.add(fk.target())) {
                againstFake(fk, fakeOrigins.get(j), recorded, found, timedOut);
            }
        }
        for (int i = 0; i < module.examples().size(); i++) {
            againstWiths(module.examples().get(i), exampleOrigins.get(i), recorded, found);
        }
        return new Readings(found, timedOut);
    }

    /**
     * The rows of one example, as much of each as is comparable.
     *
     * <p>A row is read here the way the evaluator reads it: its arity against the signature, its
     * inputs built against their parameter types, and its expectation against the output's cases and
     * then built. A row that fails any of those states nothing — each is reported as the arity, input,
     * arm or fixture error it is where the row is evaluated — and a row read otherwise here than there
     * would be held to a stand-in on an assertion the model itself refuses.
     */
    private void readRecorded(Ast.Example ex, String origin, Map<String, List<RecordedRow>> into) {
        Sig sig = sigs.get(ex.target());
        if (sig == null) {
            return;
        }
        Set<TypeName> cases = outCases(sig.outputType());
        for (Ast.ExampleRow row : ex.rows()) {
            if (row.inputs().size() != sig.inputTypes().size()) {
                continue;
            }
            Read<RecordedRow> read = within(reader -> {
                Object[] arguments = builtOrNull(reader, row.inputs(), sig.ins());
                if (arguments == null) {
                    return null;
                }
                Answered answer = readExpected(reader, row.expected(), sig.out(), cases);
                return answer instanceof Answered.Unreadable ? null
                        : new RecordedRow(new SourceRef(origin, row.expected().pos()),
                                row.expected(), arguments, answer);
            }, new Deadline.Work.Fixtures(ex.target(), origin, row.pos(),
                    row.description()));
            // A reading that did not finish is not said here, whichever reason ended it. The same row
            // is evaluated where the example is checked, which builds these fixtures and then runs the
            // behavior on top of them, so a fixture that overruns this overruns that too and is E1910
            // there, at the row.
            RecordedRow got = read.orNull();
            if (got == null) {
                continue;
            }
            into.computeIfAbsent(ex.target(), _ -> new ArrayList<>()).add(got);
        }
    }

    /** One fake against the rows recorded for the behavior it stands in for. */
    private void againstFake(Ast.Fake fk, String origin, Map<String, List<RecordedRow>> recorded,
                             List<Disagreement> found, List<UnreadFake> timedOut) {
        List<RecordedRow> rows = recorded.get(fk.target());
        Sig sig = sigs.get(fk.target());
        if (rows == null || sig == null) {
            return;
        }
        // The whole table, built the one way the proxy builds it.
        Read<Standins> read = within(
                reader -> standins(reader, fk, sig.ins(), sig.out(), new ArrayList<>()),
                new Deadline.Work.Table(fk.target(), origin, fk.pos()));
        // A switch, so that a fourth reason for a reading to end has to decide what a fake does about
        // it rather than falling in with one of these.
        switch (read) {
            // Said here, because here is where it can be. The other place a table is built is
            // `resolveFake`, which runs while a row of a behavior that *depends on* this one is
            // evaluated — and a fake nothing depends on has no such row, so an overrun that went
            // unsaid here would leave "the two agree" as the answer to a comparison never made.
            // The caret goes on the target, which is what `fk.pos()` is.
            case Read.Overspent(FailurePhase which, long limit) -> {
                timedOut.add(new UnreadFake(fk.target(), new SourceRef(origin, fk.pos()),
                        fk.target().length(), Unread.overspending(which, limit)));
                return;
            }
            case Read.StackRanOut(int depthLimit) -> {
                timedOut.add(new UnreadFake(fk.target(), new SourceRef(origin, fk.pos()),
                        fk.target().length(), new Unread.StackRanOut(depthLimit)));
                return;
            }
            case Read.Unanswered(long budgetMs) -> {
                timedOut.add(new UnreadFake(fk.target(), new SourceRef(origin, fk.pos()),
                        fk.target().length(), new Unread.DidNotAnswer(budgetMs)));
                return;
            }
            // Not about this fake. The runtime is `provided`, so a host without it builds no value at
            // all, and every fake and every row in the module would say the same thing; what was not
            // read for that reason is recorded once, where the rows are evaluated. Defensive: with no
            // runtime no recorded row builds either, and a reading with no rows read never reaches a
            // fake — so nothing arrives here today.
            case Read.RuntimeAbsent() -> {
                return;
            }
            case Read.Got(Standins _) -> { }
        }
        // The whole table or nothing: a table with a row that will not build answers nothing here,
        // and what is wrong with it is reported where the fake is written ({@link #fakeTables}).
        Standins table = read.orNull();
        if (table == null) {
            return;
        }
        for (RecordedRow row : rows) {
            Standin answering = table.answering(row.arguments());
            if (answering == null) {
                continue;   // the table answers nothing for this input; E1909's where it is used
            }
            Answered stood = new Answered.Whole(answering.answer());
            if (differs(row.answer(), stood)) {
                // The output, not the row: what disagrees is the answer, and the marker lands on it
                // the way a row's does on its expected.
                found.add(new Disagreement(fk.target(),
                        said(row.at(), row.expected(), row.answer()),
                        said(new SourceRef(origin, answering.row().output().pos()),
                                answering.row().output(), stood),
                        false));
            }
        }
    }

    /**
     * The {@code with}s on the rows of one example, against the rows recorded for the dependency each
     * stands in for — where the dependency takes no input, and there only.
     *
     * <p>A {@code with} is a fixture bound to the run of the row it is written on, not a statement
     * about the dependency. It answers whatever it is asked, but that is a fact about the function it
     * installs, not about which of the dependency's inputs it was written for: what reaches the
     * dependency is whatever the parent behavior computes and passes — a normalised field, one of two
     * branches, one of several calls — and none of that is readable from the {@code with}. Held
     * against every recorded row, it would drop the parent row's own input and read a row-local
     * assumption as a claim about all of them, so two rows faking two different answers for two
     * different orders would be reported as contradicting each other while both are right.
     *
     * <p>A dependency that takes nothing has one input, {@code ()}, so a {@code with} for it and a row
     * recorded for it are about the same call, and the comparison is the same one a {@code fake} row
     * gets. A fake row states its own inputs, which is why it needs no such condition: the recorded
     * input picks the row that answers it ({@link Standins#answering}), with nothing evaluated in between.
     *
     * <p>A {@code with} takes precedence over a {@code fake} table while the row carrying it runs
     * (see where {@link ExampleVerifier} resolves a fake). That is dispatch, and it is not brought
     * here: the table is still a
     * statement about the same behavior, written for every other row and every other run, and a
     * {@code with} beside it does not settle what it states.
     */
    private void againstWiths(Ast.Example ex, String origin, Map<String, List<RecordedRow>> recorded,
                              List<Disagreement> found) {
        for (Ast.ExampleRow row : ex.rows()) {
            for (Ast.With w : row.withs()) {
                List<RecordedRow> rows = recorded.get(w.dep());
                Sig depSig = sigs.get(w.dep());
                if (rows == null || depSig == null || !depSig.inputTypes().isEmpty()) {
                    continue;
                }
                // As with a recorded row: a `with` is written on a row, and that row is evaluated
                // where the example is checked, installing this same value. What did not finish here
                // did not finish there, and there is where it is said (E1910).
                Answered constant = within(
                        reader -> readStandIn(reader, w.value(), depSig.out(),
                                outCases(depSig.outputType())),
                        new Deadline.Work.With(w.dep(), origin, w.value().pos())).orNull();
                if (constant == null || constant instanceof Answered.Unreadable) {
                    continue;
                }
                for (RecordedRow recordedRow : rows) {
                    if (differs(recordedRow.answer(), constant)) {
                        found.add(new Disagreement(w.dep(),
                                said(recordedRow.at(), recordedRow.expected(), recordedRow.answer()),
                                said(new SourceRef(origin, w.value().pos()), w.value(), constant),
                                true));
                    }
                }
            }
        }
    }

    /**
     * One statement, with what it answers rendered — done here, where a disagreement is known, so a
     * row that agrees never pays for a description nobody reads.
     *
     * <p>The marker is measured off the written expression and not off the rendering. The rendering is
     * the value the encoder writes, which is a different length from the text it was written as — a
     * date is its ISO form, a qualified case name is its short one — so a marker measured from it
     * underlines the wrong columns and can run past the end of the line.
     */
    private Statement said(SourceRef at, Ast.Expr written, Answered asserted) {
        return new Statement(at, souther.compiler.check.Elaborator.width(written), shown(asserted));
    }

    /** What an answer says, from what was already read. Rendering from the text again would build
     * the fixture a second time — running whatever helpers it applies, outside the budget the first
     * reading was held to — and could show a value other than the one that was compared. */
    private String shown(Answered asserted) {
        return switch (asserted) {
            case Answered.CaseOnly only -> only.name().name();
            case Answered.Whole whole -> rendering.describeActual(whole.fixture().value());
            case Answered.Unreadable _ ->
                    throw new IllegalStateException("nothing was read, so nothing disagreed");
        };
    }

    /** The written inputs decoded against {@code types}, or null where one would not build — that is
     * <em>E1903</em>'s to say where the row is evaluated, and a row whose inputs are not values names
     * no input to hold a stand-in against. */
    private static Object[] builtOrNull(FixtureReader fixtures, List<Ast.Expr> written,
                                        List<BoundaryInput> types) {
        Object[] values = new Object[types.size()];
        for (int i = 0; i < types.size(); i++) {
            try {
                values[i] = fixtures.built(written.get(i), types.get(i));
            } catch (FixtureException | StackExhaustedException _) {
                return null;
            }
        }
        return values;
    }

    /**
     * One written statement about what a behavior answers, and where it is written.
     *
     * <p>{@code answer} is rendered here rather than at the report, because reading it needs the
     * decoders and the module's classes and the report has neither.
     */
    public record Statement(SourceRef at, int width, String answer) {}

    /**
     * One input for which two written statements about a behavior answer differently.
     *
     * <p>Neither side is derived from the other: the recorded row says what the behavior will owe, the
     * stand-in says what it answers while some other behavior's row runs. Which is right is not
     * readable here — a model being migrated onto may run against a stand-in while the real answer is
     * still being harvested, and that is written the way a mistake is. So both are named and neither
     * is ranked.
     *
     * <p>Independent of which source is being reported: one disagreement is projected onto both of the
     * sources its two statements are written in.
     *
     * @param viaWith whether the stand-in is a {@code with} rather than a {@code fake} row — the
     *                report names the form the author wrote, so it has to be told which one it is
     */
    public record Disagreement(String behavior, Statement recorded, Statement standIn,
                               boolean viaWith) {}

    /**
     * A fake whose table did not finish being built within the budget, so what it states and what the
     * rows recorded for the behavior state were never compared.
     *
     * <p>Carries what it takes to report it. The position and its width are measured here, where the
     * text is, the way a {@link Statement}'s are; the budget is the one the wait was actually held to,
     * rather than a second reading of the setting taken later, which a budget that stops being one
     * number for the whole compile would make wrong with nothing to say so.
     *
     * @param at where the fake names the behavior it stands in for, which is what the report marks
     */
    public record UnreadFake(String target, SourceRef at, int width, Unread why) {}

    /**
     * Why a written statement was not read.
     *
     * <p>Two things a report must not say in one voice. Spending the budget is an answer about the
     * statements, reached the same way on every host; not answering is an answer about the host, and
     * a model it is said of may be perfectly good. A single "it timed out" made a reader guess which,
     * and the guess was usually the wrong one for the model.
     */
    public sealed interface Unread {

        /** The reading spent the counted budget the policy allows. */
        record Overspent(FailurePhase which, long limit) implements Unread {}

        /** The stack ran out before the counted depth limit was reached. */
        record StackRanOut(int depthLimit) implements Unread {}

        /** The reading stopped answering within the wait it was given. */
        record DidNotAnswer(long budgetMs) implements Unread {}

        /** {@link Overspent} for whichever budget {@code which} names. */
        static Unread overspending(FailurePhase which, long limit) {
            return new Overspent(which, limit);
        }

        /**
         * Which of the three this is, as the middle of a message key.
         *
         * <p>Three messages rather than one with a reason substituted in, because the sentence is
         * mostly about what to do and that differs: a loop is bounded, a recursion is made
         * structural, and an evaluation that stopped answering is not the model's fault at all.
         *
         * <p>Callers spell out the whole key rather than build it from this, so that every key the
         * compiler names can be found by looking for it. What this saves them is the choosing.
         */
        default boolean isDepth() {
            return this instanceof Overspent(FailurePhase which, long _)
                    && which == FailurePhase.DEPTH_LIMIT;
        }

        default boolean isSteps() {
            return this instanceof Overspent(FailurePhase which, long _)
                    && which == FailurePhase.STEP_LIMIT;
        }

        default boolean isStack() {
            return this instanceof StackRanOut;
        }

        /** The limit, as written rather than as a number a locale groups: {@code 2,000} is not a
         * budget anyone set, and the settings that name these take the ungrouped form. */
        default String limitShown() {
            return switch (this) {
                case Overspent(FailurePhase _, long limit) -> Long.toString(limit);
                case StackRanOut(int depthLimit) -> Integer.toString(depthLimit);
                case DidNotAnswer(long budgetMs) -> Long.toString(budgetMs);
            };
        }
    }

    /**
     * What reading a module's written statements against each other came to.
     *
     * <p>Both lists, because a reading that did not finish and a reading that found nothing are
     * different answers and an empty list of disagreements is what the second one looks like. Which
     * of the two a compile got can otherwise turn on machine load, between a build and the next
     * keystroke in the editor.
     */
    public record Readings(List<Disagreement> disagreements, List<UnreadFake> unread) {

        public static final Readings NONE = new Readings(List.of(), List.of());

        public Readings {
            disagreements = List.copyOf(disagreements);
            unread = List.copyOf(unread);
        }
    }

    /**
     * A fake's table, decoded — the one form both the proxy and the consistency check read.
     *
     * <p>The whole table, not the part a reader happens to need. The rule that picks a row is
     * order-sensitive, so a check that re-derived it would be free to pick another; and a table is
     * valid or it is not, so a check that built only the row it was asking about would report what a
     * fake answers for a table the proxy refuses to build at all. What the report says a fake answers
     * has to be what the fake answers.
     */
    record Standins(List<Standin> explicit, Standin fallback) {

        /**
         * Which row answers {@code arguments}: the first explicit row stating them, and otherwise the
         * {@code _} row. Null where the table answers nothing, which is <em>E1909</em>'s to say where
         * the fake is used.
         *
         * <p>The table's own operation, not something a reader of it does. Both the proxy a row runs
         * against and the reading that holds the table to what the rows record ask it here, and a
         * second answer to "which row answers this" is exactly what <em>E1919</em> is for — so there
         * is one, and adding another means writing it somewhere it plainly does not belong.
         */
        Standin answering(Object[] arguments) {
            for (Standin standin : explicit) {
                if (sameArguments(standin.arguments(), arguments)) {
                    return standin;
                }
            }
            return fallback;
        }

        /** Whether a fake's row states the arguments a call arrived with, each by the language's
         * equality. A multi-input dependency is matched as a tuple (spec 22), so this walks them. */
        private static boolean sameArguments(Object[] row, Object[] key) {
            if (row.length != key.length) {
                return false;
            }
            for (int i = 0; i < row.length; i++) {
                if (!souther.runtime.Values.equal(row[i], key[i])) {
                    return false;
                }
            }
            return true;
        }
    }

    /** One row of a fake's table: the arguments it states — none, for the {@code _} row — and the
     * answer it was built into. */
    record Standin(Object[] arguments, Ast.FakeRow row, FixtureReader.BuiltFixture answer) {}

    /**
     * {@code fk}'s table, decoded against {@code ins} and {@code outType}; null (with a diagnostic
     * reported) where a row states the wrong number of inputs, or any part of any row will not
     * build — one bad row is a table the fake cannot stand in with.
     *
     * <p>Shape first, then values. A row whose input count is wrong is wrong however its output
     * builds, and building the output first would run whatever helpers it applies before saying so —
     * so a table with an arity slip and a slow or non-terminating output reported the second problem
     * instead of the first, or ran out of time before reporting either.
     */
    static Standins standins(FixtureReader fixtures, Ast.Fake fk, List<BoundaryInput> ins,
                                     BoundaryOutput outType, List<Diagnostic> out) {
        for (Ast.FakeRow r : fk.rows()) {
            if (!r.isDefault() && r.inputs().size() != ins.size()) {
                out.add(unbuildableFake(r.pos(), fk.target(), "a row has " + r.inputs().size()
                        + " input(s) where the dependency takes " + ins.size()));
                return null;
            }
        }
        List<Standin> explicit = new ArrayList<>();
        Standin fallback = null;
        try {
            for (Ast.FakeRow r : fk.rows()) {
                // A dependency that returns a sum has no single decoder; each row names one case,
                // so decode the row's output against that case's type (as an expected value is).
                FixtureReader.BuiltFixture answer = fixtures.buildFixture(r.output(), outType);
                if (r.isDefault()) {
                    fallback = new Standin(null, r, answer);
                    continue;
                }
                Object[] arguments = new Object[ins.size()];
                for (int i = 0; i < ins.size(); i++) {
                    arguments[i] = fixtures.built(r.inputs().get(i), ins.get(i));
                }
                explicit.add(new Standin(arguments, r, answer));
            }
        } catch (FixtureException fe) {
            out.add(unbuildableFake(fk.pos(), fk.target(), fe.getMessage()));
            return null;
        } catch (StackExhaustedException nt) {
            out.add(unbuildableFake(fk.pos(), fk.target(), nt.getMessage()));
            return null;
        }
        return new Standins(explicit, fallback);
    }

    /**
     * A fake that was supplied and could not be built. A dependency nothing stands in for is a different
     * problem, and saying this as that named the dependency as its own requester and reported a fake as
     * missing where one was written (issue #206).
     */
    static Diagnostic unbuildableFake(SourcePos pos, String dependency, String reason) {
        return Diagnostic.of(DiagnosticCode.E1908, "check.fake.unbuildable")
                .at(pos).args(dependency, reason).build();
    }

    /**
     * A fake whose table did not finish being built, so nothing it states was checked.
     *
     * <p>A warning, where a table that will not build is an error: waiting says that this table was
     * not read, not that it is wrong, and which of the two it is cannot be told from having waited.
     * The budget is the one this wait was held to rather than the setting read back later, and it is
     * written out rather than passed as a number, which a locale would group into a budget nobody set.
     */
    private static Diagnostic unreadableFake(Ast.Fake fk, Unread why) {
        Diagnostic.Builder said = Diagnostic.of(DiagnosticCode.E1921, why.isDepth() ? "check.fake.unchecked.deep"
                        : why.isSteps() ? "check.fake.unchecked.steps"
                        : why.isStack() ? "check.fake.unchecked.stack"
                        : "check.fake.unchecked.unanswered")
                .warning()
                .at(fk.pos(), fk.target().length())
                .args(fk.target(), why.limitShown());
        return (why.isDepth() ? said.hint("check.fake.unchecked.deep.hint", fk.target())
                : why.isSteps() ? said.hint("check.fake.unchecked.steps.hint", fk.target())
                : why.isStack() ? said.hint("check.fake.unchecked.stack.hint", fk.target())
                : said.hint("check.fake.unchecked.unanswered.hint", fk.target())).build();
    }

    // --- comparison ---------------------------------------------------------------------------

    /**
     * What someone wrote down as an answer, at the grain they wrote it.
     *
     * <p>A row may state the case and nothing under it, or the whole value, and the two sides of a
     * comparison need not have been written the same way — so what is compared is read off each side
     * once, here, rather than at every place two answers meet.
     *
     * <p>Apart from {@link FixtureReader.BuiltFixture} because the two are different things. A value
     * is built or it is not; an answer may deliberately say less than a value — a row naming a case
     * and nothing under it says only that — and only a recorded row may. Reading a stand-in as an
     * answer let a {@code with} that cannot be built at all be compared as though it named a case.
     */
    sealed interface Answered {

        /** The case, and nothing under it: a bare name denoting one. */
        record CaseOnly(TypeName name) implements Answered {}

        /** The whole value. */
        record Whole(FixtureReader.BuiltFixture fixture) implements Answered {}

        /** Nothing that can be read: a fixture that did not build or did not finish, or an
         * expectation naming a case the behavior cannot answer with. What is wrong with it is
         * reported where the row is evaluated; here it states nothing to be held against. */
        record Unreadable() implements Answered {}
    }

    /**
     * What a stand-in stands in with: the whole value, always. Unreadable where it will not build,
     * which is where it stands in for nothing at all — that is reported where the fake is resolved.
     */
    private static Answered readStandIn(FixtureReader fixtures, Ast.Expr written,
                                        BoundaryOutput outType, Set<TypeName> cases) {
        if (written == null || refusedCase(fixtures, written, cases)) {
            return new Answered.Unreadable();
        }
        try {
            return new Answered.Whole(fixtures.buildFixture(written, outType));
        } catch (FixtureException | StackExhaustedException _) {
            return new Answered.Unreadable();
        }
    }

    /**
     * What a recorded row asserts: the case alone where it named one and nothing under it, and the
     * whole value otherwise.
     *
     * <p>Built through the same builder a row's expectation goes through, so what is compared is what
     * the row asserts: a value a helper answered with is that value, not that value read back into
     * the form a fixture is written in and decoded again (issue #214).
     */
    private static Answered readExpected(FixtureReader fixtures, Ast.Expr written,
                                         BoundaryOutput outType, Set<TypeName> cases) {
        if (written == null || refusedCase(fixtures, written, cases)) {
            return new Answered.Unreadable();
        }
        if (fixtures.caseOnly(written) != null) {
            return new Answered.CaseOnly(fixtures.constructedCase(written));
        }
        try {
            return new Answered.Whole(fixtures.buildFixture(written, outType));
        } catch (FixtureException | StackExhaustedException _) {
            return new Answered.Unreadable();
        }
    }

    /** Whether {@code written} names a case the position cannot hold — <em>E1904</em> where the row
     * is evaluated, and nothing about the behavior it was written for. */
    private static boolean refusedCase(FixtureReader fixtures, Ast.Expr written,
                                       Set<TypeName> cases) {
        TypeName named = fixtures.constructedCase(written);
        return named != null && !cases.isEmpty() && !cases.contains(named);
    }

    /**
     * Whether two written answers to one input state different things.
     *
     * <p>Where either names a case and nothing more, the comparison is on the case: there is no value
     * under it to compare, and holding a full value against it would report a disagreement the row
     * never stated. The case compared is the one the value turned out to be, resolved to the type
     * this module knows it under — not the class it arrives in, which does not tell one module's
     * {@code Missing} from another's.
     *
     * <p>Where either states nothing there is nothing to disagree with. Read against a written
     * answer, silence is not a contradiction.
     */
    private static boolean differs(Answered left, Answered right) {
        if (left instanceof Answered.Unreadable || right instanceof Answered.Unreadable) {
            return false;
        }
        if (left instanceof Answered.Whole l && right instanceof Answered.Whole r) {
            return !souther.runtime.Values.equal(l.fixture().value(), r.fixture().value());
        }
        TypeName one = caseOf(left);
        TypeName other = caseOf(right);
        return one != null && other != null && !one.equals(other);
    }

    /** The case an assertion is about, or null where nothing says. */
    private static TypeName caseOf(Answered a) {
        return switch (a) {
            case Answered.CaseOnly c -> c.name();
            case Answered.Whole w -> w.fixture().caseName();
            case Answered.Unreadable _ -> null;
        };
    }
}
