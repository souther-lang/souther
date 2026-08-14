package souther.compiler.query;

import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One compile, as a set of questions that can be asked of it.
 *
 * <p>A caller sets the sources and then asks: for the classes, for a module's errors, for what a
 * name denotes. What it does with an error is its own — the batch compiler raises them together and
 * stops, an editor publishes them all per file and carries on — and that decision is the only thing
 * that differs between them. Nothing here runs a pipeline; asking a question is what makes the work
 * that answers it happen, and only that work.
 */
public final class Compilation {

    private final Db db = new Db();
    /** Which source each id was, for a caller that identifies sources by index. */
    private final Map<String, Integer> indexOfId = new LinkedHashMap<>();
    /** Whether a diagnostic of this compilation says which source it is in. A compile of one source
     *  does not: the caller knows the file it handed over. */
    private boolean saysWhichSource = true;
    /** The sources this compilation currently has, so one that goes away can be forgotten. */
    private final Set<String> held = new LinkedHashSet<>();
    /** The loader over the classes as they were when it was made, and those classes — held so that
     *  {@link #loader()} can tell whether the one it has is still a loader over what there is. */
    private ClassLoader loader;
    private Map<String, byte[]> loadedClasses;

    private Compilation() {
        // Read now, so this compilation is held to what the settings said when it started rather than
        // to what the first compile in this JVM happened to read. A caller with a reason of its own
        // says so with withEvaluationPolicy.
        db.set(new Front.Policy(), souther.compiler.examples.EvaluationPolicy.fromSettings());
    }

    /** A compile of several sources identified by their position, the way a build hands them over.
     * An import naming no module among them is resolved against {@code path}. */
    public static Compilation ofSources(List<String> sources, ModulePath path) {
        Compilation c = new Compilation();
        List<String> ids = new ArrayList<>();
        for (int i = 0; i < sources.size(); i++) {
            String id = idOfSourceIndex(i);
            ids.add(id);
            c.indexOfId.put(id, i);
            c.db.set(new Front.Text(id), sources.get(i));
        }
        c.db.set(new Front.Ids(), List.copyOf(ids));
        c.db.set(new Front.Path(), path);
        return c;
    }

    /**
     * The source id a compile handed a plain list of sources gives the {@code i}-th of them.
     *
     * <p>A build identifies its sources by where they are in the list it passed, and a result carries
     * that id back out. Both ends have to agree on it, so it is written once here rather than assumed
     * at each of them.
     *
     * <p>An id, and not a name. Nothing downstream may print one at a person or read a path out of
     * one: what to call a file is the caller's answer and depends on which others are in front of the
     * reader, so a renderer asks for it. A report printed this number where a file name belongs for
     * as long as that was left unsaid.
     */
    public static String idOfSourceIndex(int i) {
        return String.valueOf(i);
    }

    /** A compile of one source. A source with no {@code module} header takes
     * {@code defaultModuleName}, which a set of linked sources cannot allow: a module reached by an
     * import has to be named. */
    public static Compilation ofSource(String source, String defaultModuleName) {
        return ofSource(source, defaultModuleName, ModulePath.EMPTY);
    }

    /**
     * As {@link #ofSource(String, String)}, resolving an import that names no module here against
     * {@code path} — the compiled modules of the projects this one depends on.
     *
     * <p>One source is how many a caller has, not how many modules it may reach. {@code run} is
     * handed a single file and used to be given the empty path with it, which made every import of
     * another user module an unknown one; what a caller can name and what the compile can resolve
     * are separate, and this is the second of them.
     */
    public static Compilation ofSource(String source, String defaultModuleName, ModulePath path) {
        Compilation c = ofSources(List.of(source), path);
        c.db.set(new Front.DefaultName(), defaultModuleName);
        // There is only one source, so an error carries no origin: the caller knows which file it
        // handed over, and a rendered id would be a file number nobody asked for.
        c.indexOfId.clear();
        c.saysWhichSource = false;
        return c;
    }

    /**
     * A compile of a workspace, where each source is identified by the caller — a document URI.
     * {@code broken} names the modules whose sources the caller held back because they will not
     * parse, so an importer of one is left alone rather than told the module is unknown.
     */
    public static Compilation ofDocuments(Map<String, String> byId, Set<String> broken,
                                          ModulePath path) {
        Compilation c = new Compilation();
        for (Map.Entry<String, String> e : byId.entrySet()) {
            c.db.set(new Front.Text(e.getKey()), e.getValue());
        }
        c.db.set(new Front.Ids(), List.copyOf(byId.keySet()));
        c.db.set(new Front.Broken(), Set.copyOf(broken));
        c.db.set(new Front.Path(), path);
        c.held.addAll(byId.keySet());
        return c;
    }

    /**
     * The same workspace after an edit: every source as it now reads, and which modules the caller
     * is still holding back.
     *
     * <p>Nothing is thrown away. A source whose text is unchanged is unchanged, and an answer that
     * comes out the same as before leaves everything that read it alone — so what this costs is what
     * the edit actually reached.
     */
    public void update(Map<String, String> byId, Set<String> broken) {
        // A source that is gone is forgotten, along with the module it declared. Which module that
        // was has to be read before the layout is told the source is gone.
        for (String gone : List.copyOf(held)) {
            if (!byId.containsKey(gone)) {
                db.forget(gone, moduleDeclaredBy(gone));
                held.remove(gone);
            }
        }
        for (Map.Entry<String, String> e : byId.entrySet()) {
            db.set(new Front.Text(e.getKey()), e.getValue());
        }
        db.set(new Front.Ids(), List.copyOf(byId.keySet()));
        db.set(new Front.Broken(), Set.copyOf(broken));
        held.addAll(byId.keySet());
    }

    /** The module {@code id} declares, as this compilation currently has it. */
    private String moduleDeclaredBy(String id) {
        Front.Layout.Of layout = db.ask(new Front.Layout()).value();
        if (layout == null) {
            return null;
        }
        for (Map.Entry<String, String> e : layout.idOfModule().entrySet()) {
            if (e.getValue().equals(id)) {
                return e.getKey();
            }
        }
        return null;
    }

    /** A compile of one of the compiler's own core sources, which may take a reserved name. */
    public static Compilation ofCoreSource(String source) {
        Compilation c = ofSource(source, null);
        c.db.set(new Front.Core(), Boolean.TRUE);
        return c;
    }

    /** Every class this compilation generated. */
    public Map<String, byte[]> classes() {
        Map<String, byte[]> all = db.ask(new Output.All()).value();
        return all == null ? Map.of() : all;
    }

    /**
     * A loader over what this compilation produced and the modules it was compiled against — the one
     * a caller runs the generated code with.
     *
     * <p>{@link #classes()} alone is not enough to run any of it. A module resolved on the path is
     * read for its declarations and is deliberately not re-emitted here, so a behavior of this
     * compilation that builds one of its values has no class for it in this map; the path's classes
     * have to be under the map rather than beside it. Which order that is, and why a loader that
     * delegates first would answer with a stale build instead, is settled once for every caller —
     * the same composition the compile-time evaluation runs against.
     *
     * <p>The same loader for as long as the classes are the same classes. A class is its binary name
     * and the loader that defined it, so two loaders over one compilation are two definitions of
     * every type it generated, and a value made under the first is not a value of the second's
     * classes. What that looks like is a model answering wrongly: a decoded key stops equalling the
     * key a behavior looks up, so the lookup misses and the behavior answers with its default. There
     * is no exception and nothing that mentions loading. The path's classes divide the same way —
     * {@link ModulePath#loader} defines them afresh each time it is asked — so it is the composed
     * loader that is kept and not one layer of it.
     *
     * <p>Kept against the classes rather than for the life of this compilation, because an edit
     * makes a different program. {@link #classes()} answers with the map it answered with before
     * until something a generation reads changes, and with a new one after, so this follows that
     * answer rather than deciding for itself when a compilation is settled — which it never has to
     * be, nothing here running until something asks. A loader held across an edit would be one that
     * cannot see it, which is the first fault the other way round.
     */
    public ClassLoader loader() {
        Map<String, byte[]> classes = classes();
        if (loader == null || loadedClasses != classes) {
            // Built before either field is written, so a build that threw leaves this holding what it
            // held before rather than the classes it did not manage to make a loader for. Recording
            // them first would leave the two saying different things, and the next ask would read
            // that as a loader it already has — handing out the one from before the edit, which is
            // this whole method's fault with an exception in front of it.
            ClassLoader built = Output.loader(db, classes);
            loadedClasses = classes;
            loader = built;
        }
        return loader;
    }

    /** A module as everything below the check reads it — derived, desugared, and carrying the
     * recursive prelude helpers it reaches. Null where it did not get that far. */
    public Prepared module(String name) {
        return db.ask(new Shapes.Prepared(name)).value();
    }

    /** What the names in {@code module} denote — the table a question about a type is asked against. */
    public Symbols symbols(String module) {
        return db.ask(new Shapes.Scope(module)).value();
    }

    /**
     * The names of the behaviors {@code module} declares, or null where its declarations could not
     * be read.
     *
     * <p>What the source says rather than what got as far as being measured. A caller resolving a
     * name that arrived from outside needs the first: a behavior that was declared and could not be
     * prepared is a measurement that is missing, and answering "no such name" over it would report
     * the one as the other. Which is also why the unreadable case is null rather than empty — an
     * empty set is a module that declares no behavior, and that is an answer.
     */
    public Set<String> declaredBehaviors(String module) {
        return db.ask(new Front.Behaviors(module)).value();
    }

    /** The signatures of the behaviors {@code module} declares — what each takes and what it
     * answers, as the shapes a decoder and an encoder are built for. */
    public Map<String, Sig> signatures(String module) {
        Map<String, Sig> sigs = db.ask(new Bodies.Signatures(module)).value();
        return sigs == null ? Map.of() : sigs;
    }

    /** Every source id this compilation was given, in order. */
    public List<String> sourceIds() {
        List<String> ids = db.ask(new Front.Ids()).value();
        return ids == null ? List.of() : ids;
    }

    /**
     * Answers everything there is to answer about these sources — the classes, the constant
     * constructions, the examples — without deciding anything about what was found. A caller that
     * wants every problem at once asks for this and then reads {@link Db#allReports()}.
     */
    public void answerEverything() {
        structuralReports();
        db.ask(new Output.All());
        for (String module : modules()) {
            db.ask(new Output.ConstConstructions(module));
            for (String id : exampleSourcesOf(module)) {
                db.ask(Output.Examples.asked(db, module, id));
            }
            db.ask(new Output.SaidDisagreements(module));
            answerWarnings(module);
        }
    }

    /**
     * Asks every question whose whole answer is a warning, for one module.
     *
     * <p>Here rather than at each caller because there are three of them — this class and both of
     * {@link souther.compiler.Compiler}'s entry points — and a warning added to one of them is a
     * warning the other two do not report. What the editor shows and what the command line shows
     * would then differ by which list a check was written into.
     *
     * <p>Each ask answers nothing on its own; what it is for is the reports it carries.
     */
    public void answerWarnings(String module) {
        db.ask(new Names.UnusedImports(module));
        // Costs nothing unless the build asked to be told.
        db.ask(new Adequacy.Warnings(module));
    }

    /**
     * The sources that wrote any of {@code module}'s example rows or fakes, in order.
     *
     * <p>The fakes as well as the rows, because a source that wrote only a fake still has something
     * said about it: a fake that answers otherwise than a row records is reported at both, and the
     * fake's side is this source's to say.
     */
    public List<String> exampleSourcesOf(String module) {
        Set<String> distinct = new LinkedHashSet<>();
        List<String> rows = db.ask(new Front.ExampleOrigins(module)).value();
        List<String> fakes = db.ask(new Front.FakeOrigins(module)).value();
        if (rows != null) {
            distinct.addAll(rows);
        }
        if (fakes != null) {
            distinct.addAll(fakes);
        }
        return List.copyOf(distinct);
    }

    /** What this compilation was asked to measure. Set before anything is asked; the answers are
     * memoised, so a later change would leave one measured and the next not. */
    public void measure(Adequacy.Asked asked) {
        db.set(new Adequacy.Requested(), asked);
    }

    /** Measured and warned about, at {@code level}. */
    public void measure(Adequacy.Level level) {
        measure(Adequacy.Asked.warningsAt(level));
    }

    /**
     * How long this compilation gives one row to be evaluated, or one written statement to be read
     * against another. Returns this compilation, so it can be said where the sources are.
     *
     * <p>A build has no reason to say: the default is long enough that no terminating row is cut
     * short, which is the only thing a build wants from it. What is said here is said about this
     * compilation and no other, so a caller that wants a row to run out of budget — a test about what
     * is reported when one does not come back — gets that without holding every other compile in the
     * same JVM to the same wait.
     *
     * @throws IllegalArgumentException if {@code budget} is not positive; a row that is given no time
     *     at all would report every behavior as one that does not terminate.
     */
    public Compilation withExampleBudget(java.time.Duration budget) {
        long ms = budget.toMillis();
        if (ms <= 0) {
            throw new IllegalArgumentException("an example budget has to be positive: " + budget);
        }
        db.set(new Front.ExampleBudget(), ms);
        return this;
    }

    /**
     * What this compilation gives one row or one reading to finish within, said outright. Returns
     * this compilation, so it can be said where the sources are.
     *
     * <p>For a test that is asking what the compiler says about work that did not come back. Written
     * with a budget, that test has to write a model that does not terminate and then race a clock to
     * see it reported — and a loaded host loses the race in the direction that matters, reporting
     * work that finished as work that did not. A deadline that decides by what the work is says the
     * same thing as a fact. A build has no reason to set one; see {@link #withExampleBudget}.
     */
    public Compilation withDeadline(souther.compiler.examples.Deadline deadline) {
        db.set(new Front.ExampleDeadline(), deadline);
        return this;
    }

    /**
     * What this compilation allows one row's evaluation. Returns this compilation, so it can be said
     * where the sources are.
     *
     * <p>A build has no reason to say: the default is set so that no row a model states reaches it.
     * What a caller says here is said about this compilation alone, so a test holding a row to a few
     * steps does not hold every other compile in the same JVM to them.
     */
    public Compilation withEvaluationPolicy(souther.compiler.examples.EvaluationPolicy policy) {
        db.set(new Front.Policy(), policy);
        return this;
    }

    /** How well one module's rows cover it. {@link #answerEverything()} need not have run: the
     * measures ask for what they read. */
    public Adequacy.Of adequacy(String module) {
        return new Adequacy.Of(db.ask(new Adequacy.Witnesses(module)).value(),
                db.ask(new Adequacy.Coverage(module)).value(),
                db.ask(new Adequacy.BranchCoverage(module)).value());
    }

    public Db db() {
        return db;
    }

    /** The names of the modules these sources declare, in the order the sources were given. */
    public List<String> modules() {
        List<String> declared = db.ask(new Front.Declared()).value();
        return declared == null ? List.of() : declared;
    }

    /** The id of the source that declares {@code module}, or null when nothing here does. */
    public String sourceIdOf(String module) {
        Front.Layout.Of layout = db.ask(new Front.Layout()).value();
        return layout == null ? null : layout.idOfModule().get(module);
    }

    /**
     * The module {@code sourceId} is part of — the one it declares, or the one its rows are for —
     * or null when this compilation does not have the source.
     *
     * <p>The other direction of {@link #sourceIdOf}, and not its inverse: a module is declared in
     * one source, and several sources may be part of it.
     */
    public String moduleOf(String sourceId) {
        return db.ask(new Front.ModuleOf(sourceId)).value();
    }

    /**
     * The problems that stop this compilation before any module is looked at: a source that names a
     * module twice, one that shadows a module already on the path, and a cycle among them.
     *
     * <p>These come first because each one makes "which module is this name" unanswerable, and
     * every question below that is about a name.
     */
    public List<Db.Found> structuralReports() {
        List<Db.Found> found = new ArrayList<>();
        Answer<Front.Layout.Of> layout = db.ask(new Front.Layout());
        for (Report report : layout.reports()) {
            found.add(new Db.Found(null, null, report));
        }
        for (String id : sourceIds()) {
            for (Report report : db.ask(new Front.Declares(id)).reports()) {
                found.add(new Db.Found(null, id, report));
            }
            for (Report report : db.ask(new Front.AttachedTo(id)).reports()) {
                found.add(new Db.Found(null, id, report));
            }
        }
        for (String module : modules()) {
            for (Report report : db.ask(new Front.ShadowsPath(module)).reports()) {
                found.add(new Db.Found(module, null, report));
            }
            for (Report report : db.ask(new Names.InCycle(module)).reports()) {
                found.add(new Db.Found(module, null, report));
            }
        }
        return found;
    }

    /**
     * Every problem these sources have, on the source it belongs to. A source with none maps to an
     * empty list.
     *
     * <p>Where a report goes is the report's to say, not this method's: an error in an imported
     * module lands on that module's document however far away it was asked for, and a failing
     * example row lands on the file the row was written in. A report about something the caller does
     * not have — a module read off the path — has nowhere to go and is left out.
     *
     * <p>This is the only place one report becomes several entries. A problem written in two files is
     * said in both, so an author editing either is told, and each entry carries the source its
     * primary region is in — which is not the file it is filed under, for the file that holds the
     * other half. A reader turns that pair into what to quote and what to link to
     * ({@link souther.compiler.diag.DiagnosticView}).
     */
    public Map<String, List<Located>> diagnostics() {
        answerEverything();
        Map<String, List<Located>> byId = new LinkedHashMap<>();
        for (String id : sourceIds()) {
            byId.put(id, new ArrayList<>());
        }
        for (Db.Found found : db.allReports()) {
            String primary = locatedSourceIdOf(found);
            for (String id : publishSourceIdsOf(found)) {
                List<Located> on = byId.get(id);
                if (on != null) {
                    on.add(new Located(found.report().diagnostic(), primary));
                }
            }
        }
        Map<String, List<Located>> published = new LinkedHashMap<>();
        byId.forEach((id, found) -> published.put(id, List.copyOf(found)));
        return published;
    }

    /**
     * The errors among {@code found} as one exception, the first of them leading — or null when
     * nothing there is an error.
     *
     * <p>Every error, not the first. A compilation answers each of its questions and files what it
     * found, so by the time anything asks for the failure they are all in hand; handing back one of
     * them sends the author to fix that one and compile again to be told the next, which the
     * compiler already knew. The exception carries a list, and the command line and
     * {@code --format json} render each of them, so nothing between here and the author needs them
     * to be one.
     *
     * <p>Leading matters because a caller reading {@link CompileException#code()} or its message
     * reads the first, and that is the error a reader is sent to first. First means first in the
     * order the sources were given, then where in the source it is — not first worked out. A
     * question is answered when something asks it, and what asks first is an implementation detail:
     * resolving one module's names reaches another module's, so ordering by that would let moving a
     * report earlier in the compiler change which file a batch compile sends the author to. A report
     * about no source in particular comes before all of them, and one about no position before the
     * rest of its source.
     *
     * <p>The order the sources were given is the index a compile of a list of them assigns
     * ({@link #ofSources}). A compile of documents assigns none — a workspace has no first file —
     * and there the reports fall together and are ordered by position alone. What asks this is a
     * batch compile; an editor reads {@link #diagnostics()}, which files each report under the
     * source it is in and never has the question.
     *
     * <p>Two reports at one position keep the order the checker produced them in — a stable sort is
     * what that takes. A check that reports each of its own violations puts them all at the
     * declaration it is about, so this is the ordinary case rather than a tie to break arbitrarily.
     *
     * <p>Where a diagnostic is says where to look, and nothing about what caused what. An error a
     * checker reports off a value another error produced — a name that resolved to nothing, a body
     * that could not be typed — can be written to the left of the error it came from, and then it
     * leads. That is not this order failing to find the cause: a cause is not recoverable from two
     * positions, and a secondary diagnostic is the checker's to withhold where it should not be said
     * at all. This decides how the errors are presented; whether one of them should have been
     * reported is the checker's own question.
     */
    public CompileException failure(List<Db.Found> found) {
        List<Db.Found> errors = new ArrayList<>();
        for (Db.Found f : found) {
            if (f.report().isError()) {
                errors.add(f);
            }
        }
        if (errors.isEmpty()) {
            return null;
        }
        errors.sort(Comparator.comparingInt(this::orderOf)
                .thenComparingInt(f -> lineOf(f.report().diagnostic()))
                .thenComparingInt(f -> columnOf(f.report().diagnostic())));
        Db.Found first = errors.get(0);
        List<Diagnostic> rest = new ArrayList<>();
        List<String> restSources = new ArrayList<>();
        for (Db.Found f : errors.subList(1, errors.size())) {
            rest.add(f.report().diagnostic());
            restSources.add(sourceIdOf(f));
        }
        return first.report().asException()
                .alsoReporting(rest, restSources)
                .inSource(sourceIdOf(first));
    }

    /** Where a report sits among the sources for ordering, with the one naming none before them all. */
    private int orderOf(Db.Found found) {
        int index = indexOf(found);
        return index < 0 ? -1 : index;
    }

    /** A report with no position comes before the ones in its source that have one: it is about the
     *  source rather than about a line of it. */
    private static int lineOf(Diagnostic diagnostic) {
        SourcePos pos = diagnostic == null ? null : diagnostic.pos();
        return pos == null ? -1 : pos.line();
    }

    private static int columnOf(Diagnostic diagnostic) {
        SourcePos pos = diagnostic == null ? null : diagnostic.pos();
        return pos == null ? -1 : pos.column();
    }

    /**
     * Which of the sources this compilation holds a report's primary region is in: the one the report
     * claims ({@link Db.Found#claimedSourceId()}), or — where it claims none, or claims one this
     * compile was not handed — the one that declares the module it was about.
     *
     * <p>The second half of that is a guard, and it guards availability as much as attribution. A
     * position may have been read from a source this compile does not have: the prelude, or a module
     * read back off the module path. Filing a report under a name {@link #diagnostics()} has no entry
     * for would drop it silently, and a report the author never sees is worse than one on the wrong
     * file.
     *
     * <p>Always answered, whatever the compile tells a caller about its sources. What a source is
     * called here is how a report is filed and how its regions are quoted; what a caller is told is
     * {@link #sourceIdOf(Db.Found)}, and the two are not the same question.
     */
    private String locatedSourceIdOf(Db.Found found) {
        String claimed = found.claimedSourceId();
        if (claimed != null && sourceIds().contains(claimed)) {
            return claimed;
        }
        return found.module() == null ? null : sourceIdOf(found.module());
    }

    /**
     * Which source a report's primary region is in, as a caller holding its own list of files is
     * told — none, for a compile of one source, where that caller knows the file it handed over.
     */
    public String sourceIdOf(Db.Found found) {
        return saysWhichSource ? locatedSourceIdOf(found) : null;
    }

    /**
     * Every source a report is said at, the one its primary region is in first. One entry for nearly
     * everything; several for a problem that belongs to each of the places it points at and to none
     * of them more.
     *
     * <p>Read off the regions rather than off a list of files, so every entry is somewhere the
     * report has something to show.
     */
    public List<String> publishSourceIdsOf(Db.Found found) {
        String primary = locatedSourceIdOf(found);
        List<String> saidAt = new ArrayList<>();
        if (primary != null) {
            saidAt.add(primary);
        }
        if (found.report().delivery().saidAtEveryRegion()) {
            for (LabeledRegion label : found.report().diagnostic().secondary()) {
                String where = label.sourceIdOr(primary);
                if (where != null && !saidAt.contains(where)) {
                    saidAt.add(where);
                }
            }
        }
        return List.copyOf(saidAt);
    }

    /** Where a report sits in the order the sources were given, or -1 when it names none. Only for
     * ordering: which file a reader is sent to is {@link #sourceIdOf(Db.Found)}. */
    private int indexOf(Db.Found found) {
        String id = locatedSourceIdOf(found);
        if (id == null) {
            return -1;
        }
        Integer index = indexOfId.get(id);
        return index == null ? -1 : index;
    }

    /**
     * The warnings among {@code found}, in order, each tagged with the source its primary region is
     * in — the same tag {@link #failure} puts on an error, so a warning can be quoted where it is.
     *
     * <p>One entry per warning, never one per file it is said at. A problem written in two files is
     * one thing to be told about on a terminal; the second telling is what an editor needs, and that
     * is {@link #diagnostics()}.
     */
    public List<Located> warnings(List<Db.Found> found) {
        List<Located> warnings = new ArrayList<>();
        for (Db.Found f : found) {
            if (!f.report().isError()) {
                warnings.add(new Located(f.report().diagnostic(), sourceIdOf(f)));
            }
        }
        return warnings;
    }

    /**
     * The errors among {@code found}, tagged as {@link #warnings} tags a warning.
     *
     * <p>All of them, where {@link #failure} answers with one. A caller that stops at the first
     * error wants the first; one that goes on to say something about the whole compilation has
     * already read past it, and showing a reader one error beside an account of everything else
     * would leave them to wonder what the rest of the errors were.
     */
    public List<Located> errors(List<Db.Found> found) {
        List<Located> errors = new ArrayList<>();
        for (Db.Found f : found) {
            if (f.report().isError()) {
                errors.add(new Located(f.report().diagnostic(), sourceIdOf(f)));
            }
        }
        return errors;
    }
}
