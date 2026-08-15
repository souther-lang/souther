package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Exposing;
import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.diag.CompileException;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The modules one set of published classes declares, read as the compiler reads them.
 *
 * <p>What a declaration means is the front end's answer and not something read off its text: which
 * declaration a name reaches, whether a name is a local binding or something declared elsewhere,
 * what a bare name an import brought in stands for. So a reader that has to compare two builds'
 * declarations reads both through this, and compares what comes back rather than what was written.
 *
 * <p>Everything here is the compiler's own: {@link PublishedModule} puts the declarations back
 * together as source, {@link Exposing} reads what the import lines bring in, and {@link Resolve}
 * answers every name. What this adds is only which modules to read — a module's declarations reach
 * the modules they name, and those have to be in sight for a name to be resolved against them.
 *
 * <p>Not the query layer, because there are two universes and a compilation has one. The classes an
 * answer brings are not on this compile's path and never will be; they are a second set of
 * declarations to be read the same way, which is what this is for.
 */
public final class PublishedUniverse {

    private final PublishedModule.Classes classes;
    private final Map<String, Ast.Module> written = new LinkedHashMap<>();
    private final Map<String, Exposing.Checked> checked = new LinkedHashMap<>();
    private final Map<String, Hir.Module> resolved = new LinkedHashMap<>();
    private final Set<String> unreadable = new LinkedHashSet<>();

    private PublishedUniverse(PublishedModule.Classes classes) {
        this.classes = classes;
    }

    /** The universe those classes declare. Nothing is read until a module is asked for. */
    public static PublishedUniverse of(PublishedModule.Classes classes) {
        return new PublishedUniverse(classes);
    }

    /**
     * {@code module} as the front end reads it, or null where these classes do not declare it or
     * this compiler cannot read what they published.
     *
     * <p>Read once. A module is resolved against every module its declarations reach, so asking for
     * one reads the ones it names — and the modules those name, since a type of an imported type is
     * reached the same way.
     */
    public Hir.Module resolved(String module) {
        Hir.Module already = resolved.get(module);
        if (already != null || unreadable.contains(module)) {
            return already;
        }
        readReaching(module);
        if (!written.containsKey(module)) {
            unreadable.add(module);
            return null;
        }
        Registry<Ast.Def> registry = Registry.ofWritten(Map.copyOf(written));
        for (Map.Entry<String, Ast.Module> each : Map.copyOf(written).entrySet()) {
            if (resolved.containsKey(each.getKey())) {
                continue;
            }
            Hir.Module hir = resolve(each.getValue(), registry, checked.get(each.getKey()));
            if (hir == null) {
                unreadable.add(each.getKey());
            } else {
                resolved.put(each.getKey(), hir);
            }
        }
        return resolved.get(module);
    }

    /**
     * Whether these classes say anything at all about {@code module}, as against saying something
     * this compiler cannot read.
     *
     * <p>Asked of the classes rather than of what was read: a module whose declarations came back
     * unreadable is one these classes do carry, and a reader deciding what to say about it needs the
     * two apart. Nothing is published for a name is one thing to tell someone; what is published
     * cannot be read here is another.
     */
    public boolean declares(String module) {
        return classes.of(souther.compiler.jvm.SoutherJvmAbi.nameOf(
                new souther.compiler.jvm.GeneratedClass.ModuleDeclarations(module)).binaryName())
                != null;
    }

    /** Reads {@code module} and everything its declarations name, as far as these classes go. */
    private void readReaching(String module) {
        Deque<String> toRead = new ArrayDeque<>(Set.of(module));
        Set<String> tried = new LinkedHashSet<>(Set.of(module));
        while (!toRead.isEmpty()) {
            String name = toRead.removeFirst();
            if (written.containsKey(name) || unreadable.contains(name)) {
                continue;
            }
            Exposing.Checked read = read(name);
            if (read == null) {
                unreadable.add(name);
                continue;
            }
            written.put(name, read.module());
            checked.put(name, read);
            // Which modules a module's declarations name, answered where the compiler answers it:
            // an import line names one, and so does a type or a behavior written with a qualifier,
            // which needs no import at all.
            for (String reaches : souther.compiler.query.Front.reaches(read.module()).keySet()) {
                if (tried.add(reaches)) {
                    toRead.addLast(reaches);
                }
            }
        }
    }

    /**
     * What {@code module} published, with its import lines read.
     *
     * <p>Every way of failing is an absence rather than a raise. These classes came from wherever
     * the answer was built: they may carry nothing, carry declarations at another boundary revision,
     * or not be class files this JVM reads. What a reader of this does about any of them is the
     * same, and it is the reader's to decide rather than this walk's to impose.
     */
    private Exposing.Checked read(String module) {
        try {
            PublishedModule published = PublishedModule.read(module, classes);
            return published == null ? null : Exposing.check(published.module());
        } catch (CompileException | IllegalArgumentException _) {
            return null;
        }
    }

    /** {@code module} with every name it writes answered, or null where a name could not be. */
    private static Hir.Module resolve(Ast.Module module, Registry<Ast.Def> registry,
                                      Exposing.Checked exposed) {
        SyntaxSymbols symbols = SyntaxSymbols.of(module.name(), registry,
                denotations(registry, module), aliases(module));
        Resolve.Values base = Resolve.Values.of(module);
        Resolve.Values values = new Resolve.Values(base.module(), base.helpers(), base.behaviors(),
                base.behaviorsWhole(), exposed.exposed(), base.elsewhere());
        Resolve.Resolution resolution = Resolve.resolving(module, symbols, values);
        return resolution.unresolved().isEmpty() ? resolution.module() : null;
    }

    /**
     * What a bare type name means here: this module's own declarations, and what its imports name.
     *
     * <p>Every identity is the declaration world's answer ({@link Registry#identify}) rather than one
     * made here from a module and a spelling. A published module was compiled before it was
     * published, so what it declares is settled; what this does is say which of those a bare name in
     * it reaches, which is what resolution is handed.
     */
    private static Map<String, souther.compiler.types.Denotation> denotations(
            Registry<Ast.Def> registry, Ast.Module module) {
        Map<String, souther.compiler.types.Denotation> names = new LinkedHashMap<>();
        for (Ast.Def own : registry.declaredIn(module.name()).values()) {
            souther.compiler.types.TypeSymbol declares = registry.identify(own.declaredKey());
            if (declares != null) {
                names.put(own.name(), new souther.compiler.types.Denotation.Denotes(declares));
            }
        }
        for (Ast.Import imported : module.imports()) {
            for (Ast.ImportedName brought : imported.importedNames()) {
                souther.compiler.types.TypeSymbol denotes =
                        registry.identify(new souther.compiler.types.TypeKey(imported.module(),
                                brought.written().canonical()));
                if (denotes != null) {
                    names.put(brought.written().canonical(),
                            new souther.compiler.types.Denotation.Denotes(denotes));
                }
            }
        }
        return names;
    }

    /** Which module each qualifier stands for. */
    private static Map<String, String> aliases(Ast.Module module) {
        Map<String, String> aliases = new LinkedHashMap<>();
        for (Ast.Import imported : module.imports()) {
            if (imported.alias() != null) {
                aliases.put(imported.alias(), imported.module());
            }
        }
        return aliases;
    }
}
