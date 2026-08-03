package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One compile, as a set of questions that can be asked of it.
 *
 * <p>A caller sets the sources and then asks: for the classes, for a module's errors, for what a
 * name denotes. What it does with an error is its own — the batch compiler raises the first, an
 * editor publishes them all per file — and that decision is the only thing that differs between
 * them. Nothing here runs a pipeline; asking a question is what makes the work that answers it
 * happen, and only that work.
 */
public final class Compilation {

    private final Db db = new Db();
    /** Which source each id was, for a caller that names sources by index. */
    private final Map<String, Integer> indexOfId = new LinkedHashMap<>();
    /** The sources this compilation currently has, so one that goes away can be forgotten. */
    private final Set<String> held = new LinkedHashSet<>();

    private Compilation() {}

    /** A compile of several sources named by their position, the way a build hands them over. An
     * import naming no module among them is resolved against {@code path}. */
    public static Compilation ofSources(List<String> sources, ModulePath path) {
        Compilation c = new Compilation();
        List<String> ids = new ArrayList<>();
        for (int i = 0; i < sources.size(); i++) {
            String id = String.valueOf(i);
            ids.add(id);
            c.indexOfId.put(id, i);
            c.db.set(new Front.Text(id), sources.get(i));
        }
        c.db.set(new Front.Ids(), List.copyOf(ids));
        c.db.set(new Front.Path(), path);
        return c;
    }

    /** A compile of one self-contained source. A source with no {@code module} header takes
     * {@code defaultModuleName}, which a set of linked sources cannot allow: a module reached by an
     * import has to be named. */
    public static Compilation ofSource(String source, String defaultModuleName) {
        Compilation c = ofSources(List.of(source), ModulePath.EMPTY);
        c.db.set(new Front.DefaultName(), defaultModuleName);
        // There is only one source, so an error carries no origin: the caller knows which file it
        // handed over, and a rendered index would be a file number nobody asked for.
        c.indexOfId.clear();
        return c;
    }

    /**
     * A compile of a workspace, where each source is named by the caller — a document URI.
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

    /** A module as everything below the check reads it — derived, desugared, and carrying the
     * recursive prelude helpers it reaches. */
    public Ast.Module module(String name) {
        return db.ask(new Shapes.Prepared(name)).value();
    }

    /** The signatures of the behaviors {@code module} declares. */
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
                db.ask(new Output.Examples(module, id));
                db.ask(new Output.SaidDisagreements(module, id));
            }
            // One ask, which answers nothing and costs nothing unless the build asked to be told.
            db.ask(new Adequacy.Warnings(module));
        }
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

    /** Which source declares {@code module}, as the index a diagnostic names, or -1 when this
     * compilation names its sources some other way. */
    public int sourceIndexOf(String module) {
        Front.Layout.Of layout = db.ask(new Front.Layout()).value();
        String id = layout == null ? null : layout.idOfModule().get(module);
        Integer index = id == null ? null : indexOfId.get(id);
        return index == null ? -1 : index;
    }

    /** The index a diagnostic names for a source id, or -1 when this compilation names its sources
     * some other way. */
    public int sourceIndexOfId(String id) {
        Integer index = indexOfId.get(id);
        return index == null ? -1 : index;
    }

    /** The id of the source that declares {@code module}, or null when nothing here does. */
    public String sourceIdOf(String module) {
        Front.Layout.Of layout = db.ask(new Front.Layout()).value();
        return layout == null ? null : layout.idOfModule().get(module);
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
     */
    public Map<String, List<Diagnostic>> diagnostics() {
        answerEverything();
        Map<String, List<Diagnostic>> byId = new LinkedHashMap<>();
        for (String id : sourceIds()) {
            byId.put(id, new ArrayList<>());
        }
        for (Db.Found found : db.allReports()) {
            String id = found.sourceId() != null ? found.sourceId() : sourceIdOf(found.module());
            List<Diagnostic> on = id == null ? null : byId.get(id);
            if (on != null) {
                on.add(found.report().diagnostic());
            }
        }
        Map<String, List<Diagnostic>> published = new LinkedHashMap<>();
        byId.forEach((id, found) -> published.put(id, List.copyOf(found)));
        return published;
    }

    /**
     * The first error among {@code found}, as the exception the pass raised, tagged with the source
     * it belongs to — or null when nothing there is an error.
     *
     * <p>First means first in the order the sources were given, not first worked out. A question is
     * answered when something asks it, and what asks first is an implementation detail: resolving one
     * module's names reaches another module's, so moving a report earlier in the compiler would
     * otherwise change which file a batch compile sends the author to. A report about no source in
     * particular comes before all of them.
     */
    public CompileException firstError(List<Db.Found> found) {
        Db.Found first = null;
        int at = Integer.MAX_VALUE;
        for (Db.Found f : found) {
            if (!f.report().isError()) {
                continue;
            }
            int index = indexOf(f);
            int order = index < 0 ? -1 : index;
            if (order < at) {
                first = f;
                at = order;
            }
        }
        return first == null ? null : first.report().asException().inSource(indexOf(first));
    }

    /** Which source a report belongs to: the one it named, or the one that declares the module it
     * was about, or none. */
    public int indexOf(Db.Found found) {
        if (found.sourceId() != null) {
            Integer index = indexOfId.get(found.sourceId());
            return index == null ? -1 : index;
        }
        return found.module() == null ? -1 : sourceIndexOf(found.module());
    }

    /** The warnings among {@code found}, in order, each tagged with the source it belongs to — the
     *  same tag {@link #firstError} puts on an error, so a warning can be quoted where it is. */
    public List<Located> warnings(List<Db.Found> found) {
        List<Located> warnings = new ArrayList<>();
        for (Db.Found f : found) {
            if (!f.report().isError()) {
                warnings.add(new Located(f.report().diagnostic(), indexOf(f)));
            }
        }
        return warnings;
    }
}
