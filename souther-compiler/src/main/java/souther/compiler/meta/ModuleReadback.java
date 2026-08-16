package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.check.Exposing;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Reading a module back from what {@link ModuleMetadata} wrote into its classes: the declarations
 * another project needs in order to {@code import} it, without its {@code .sou}.
 *
 * <p>The declarations are put back together as one source and handed to the parser, so what an
 * importing project sees is what the declaring project wrote, read by the same front end. What comes
 * back of the module's implementation is what its declarations cannot be read without: the helpers
 * an invariant calls, and the {@code let}s it publishes, which a reader substitutes and expands for
 * itself. Every other body stays where it was written.
 *
 * <p>Travelling as source is also what a published body's meaning rests on. A helper is read back by
 * the same rule that read it in the first place, so one whose parameter types its body settles
 * arrives with no types written and is settled again here — including one that names what a value is
 * and leaves what it holds open, which is why no type variable has to be written for it to cross.
 *
 * <p>Reading the import lines is part of reading the module and not a step after it. A module comes
 * out of here with its library names already answered ({@link ReadableModule}), because the lines
 * that carried them are dropped once read and nothing else says what its bare names mean. Split in
 * two, a caller did the first and not the second, and an invariant that called a name its module
 * imported bare then resolved against nothing in every project but the one that wrote it.
 *
 * <p>Nothing here raises for an artifact this compiler will not read. Every such failure is a
 * {@link Readback.Failure}, named where it is found by the code that knows its shape, so what
 * converts is stated rather than decided by how wide a caller's catch happened to be.
 *
 * <p>One raise is turned into a failure here, the parser's, and the catch is around the parse
 * alone. The other physical way a reading fails — bytes this runtime does not read — is answered
 * as a value by {@link PublishedClasses}, which is where the bytes are and so the only place that
 * knows what went wrong with them. Nothing here reads an exception type as a statement about
 * somebody's artifact.
 */
public final class ModuleReadback {

    private ModuleReadback() {}

    /**
     * Where the code of {@code module} is written, as anything reading it back says so.
     *
     * <p>One function, because there is one answer and two callers. This is what stamps the parse,
     * and a report about a module that never got as far as being parsed — an artifact at a boundary
     * revision this compiler does not agree with, one whose declaration class is missing — has no
     * position to read a provenance off and its name is all there is. Written out at both, the two
     * agree only for as long as provenance is a module name and nothing else; the day it carries
     * where the published source is, this is the one place that learns it.
     */
    public static SourceProvenance provenanceOf(String module) {
        return new SourceProvenance.APublishedModule(module);
    }

    /**
     * Whether {@code classes} say anything at all about {@code module}, as against saying something
     * this compiler will not read.
     *
     * <p>Asked of the classes, and not by reading. Whether the path carries a name is settled by
     * whether there is a class of it with declarations on it; whether what those declarations say
     * can be read back is a further question with its own answer, and a caller that wanted only the
     * first used to get it by doing the whole reading and looking at what came out. That put every
     * way a readback can fail into the failure domain of a question that does not depend on any of
     * them — a module compiled here that also sits on the path, in a jar built by another compiler,
     * ended the compilation from a question whose whole answer is yes or no.
     */
    public static boolean carry(String module, PublishedClasses classes) {
        return switch (classes.of(declarationsClassOf(module))) {
            case PublishedClasses.Carried.NoSuchClass _ -> false;
            // Carried, and not readable. Those are the two questions this whole reading is written
            // to keep apart, and folding the second into "no such name" here would have answered
            // one of them with the other — the same collapse, at the one query that was meant not
            // to depend on the reading at all.
            case PublishedClasses.Carried.UnreadableMetadata _ -> true;
            case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                    d.module() != null;
        };
    }

    /** What {@code classes} carry for {@code moduleName}. */
    public static Readback read(String moduleName, PublishedClasses classes) {
        PublishedClasses.Declarations found;
        switch (classes.of(declarationsClassOf(moduleName))) {
            case PublishedClasses.Carried.NoSuchClass _ -> {
                return new Readback.SaysNothing();
            }
            case PublishedClasses.Carried.UnreadableMetadata _ -> {
                return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
            }
            case PublishedClasses.Carried.Declared(PublishedClasses.Declarations declared) ->
                    found = declared;
        }
        if (found.module() == null) {
            return new Readback.SaysNothing();   // a class this compiler put no declarations on
        }
        PublishedClasses.SoutherModuleView m = found.module();
        // A member this compiler asks for and the writer did not write reads as its default. The
        // header is the one that cannot be defaulted — without it there is no module to parse — so a
        // module that carries none was written by something this compiler does not agree with,
        // whatever its number says.
        if (m.compat() != Backend.BOUNDARY_VERSION || m.header().isBlank()) {
            return unreadable(moduleName, new Readback.Failure.Incompatible(m.compiler()));
        }
        StringBuilder declarations = new StringBuilder();
        Set<String> injected = new LinkedHashSet<>();
        for (String type : m.types()) {
            PublishedClasses.Declarations carried;
            switch (classes.of(moduleName + "." + type)) {
                case PublishedClasses.Carried.UnreadableMetadata _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.UnreadableMetadata());
                }
                case PublishedClasses.Carried.NoSuchClass _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.DeclarationMissing(type));
                }
                case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                        carried = d;
            }
            if (carried.data() == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(type));
            }
            declarations.append('\n').append(carried.data()).append('\n');
        }
        for (String behavior : m.behaviors()) {
            PublishedClasses.Declarations carried;
            switch (classes.of(SoutherJvmAbi.nameOf(
                    new GeneratedClass.BehaviorInterface(moduleName, behavior)).binaryName())) {
                case PublishedClasses.Carried.UnreadableMetadata _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.UnreadableMetadata());
                }
                case PublishedClasses.Carried.NoSuchClass _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.DeclarationMissing(behavior));
                }
                case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                        carried = d;
            }
            if (carried.behaviorSignature() == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(behavior));
            }
            declarations.append('\n').append(carried.behaviorSignature()).append('\n');
            if (Boolean.TRUE.equals(carried.behaviorInjected())) {
                injected.add(behavior);
            }
        }
        for (String helper : m.invariantHelpers()) {
            declarations.append('\n').append(helper).append('\n');
        }
        StringBuilder source = new StringBuilder(m.header()).append('\n');
        for (String line : m.imports()) {
            source.append(line).append('\n');
        }
        source.append(declarations);
        Ast.Module parsed;
        try {
            // Read back, not read: the text was put together here out of what the module carries, so
            // its lines are lines of nothing anybody holds. Every position it makes says so from the
            // start, and a reader here reaches the module by its name.
            parsed = CstFrontend.parseWhatAModulePublished(source.toString(),
                    provenanceOf(moduleName));
        } catch (CompileException _) {
            // Around the parse and nothing else. A pass raises, so this is the one place a raise has
            // to be turned into a failure — and wrapping any more than the call would let something
            // else's raise arrive as a statement about this artifact.
            return unreadable(moduleName, new Readback.Failure.InvalidPublishedSyntax());
        }
        if (!parsed.name().equals(moduleName)) {
            // A reading answers about the module it was asked for. The class was found by that name
            // and the module is named by the header on it; where the two differ there is no reading
            // of this module here, whatever the class carries.
            return unreadable(moduleName, new Readback.Failure.AnotherModule(parsed.name()));
        }
        // Which imports are needed is asked of the header and the declarations — everything that was
        // published except the import lines themselves.
        Exposing.Checked checked =
                Exposing.check(withNeededImports(parsed, m.header() + "\n" + declarations));
        if (!checked.refused().isEmpty()) {
            List<Readback.Exposure> crossed = checked.refused().stream()
                    .map(ModuleReadback::asAnArtifactsFailure).toList();
            return unreadable(moduleName, new Readback.Failure.InvalidExposure(
                    crossed.get(0), crossed.subList(1, crossed.size())));
        }
        return new Readback.Ready(
                new AsRead(checked.module(), injected, checked.exposed()));
    }

    /**
     * The only {@link ReadableModule} there is.
     *
     * <p>Package-private, and built at one statement of {@link #read}. Nothing outside this package
     * can make one, and nothing inside it does — so a value of this type is a reading that got to
     * the end, rather than a value somebody assembled that looks like one.
     */
    record AsRead(Ast.Module module, Set<String> injectedBehaviors,
                  Map<String, ValueName.Stdlib> libraryNames) implements ReadableModule {

        /** Copied, because this is an answer a compilation remembers and an answer it remembers is
         *  a value. */
        AsRead {
            injectedBehaviors = Collections.unmodifiableSet(new LinkedHashSet<>(injectedBehaviors));
            libraryNames = Collections.unmodifiableMap(new LinkedHashMap<>(libraryNames));
        }
    }

    private static Readback unreadable(String module, Readback.Failure why) {
        return new Readback.Unreadable(module, why);
    }

    /**
     * A refusal the check found, as a fact about the artifact it was found in.
     *
     * <p>The place goes here and nowhere else. A refusal carries the {@code import} line it was
     * written on, which is what lets a reader holding that source quote it; this side has no source
     * to quote and the line is in a text nobody holds, so what crosses is what happened. Left on,
     * the position this whole type exists to keep out would have arrived as an AST node instead of
     * as a diagnostic.
     *
     * <p>A switch over every refusal there is, with nothing to fall through to: a rule added to the
     * check is one this boundary has to say something about, and one that reached here with nothing
     * to say would be an artifact refused for a reason nobody can name.
     */
    private static Readback.Exposure asAnArtifactsFailure(Exposing.Refusal refusal) {
        return switch (refusal) {
            case Exposing.Refusal.NoSuchLibraryFunction r ->
                    new Readback.Exposure.NoSuchLibraryFunction(r.imp().module(), r.name());
            case Exposing.Refusal.BroughtTwice r ->
                    new Readback.Exposure.BroughtTwice(r.imp().module(), r.name(),
                            r.earlier().qualified());
            case Exposing.Refusal.CollidesWithADeclaration r ->
                    new Readback.Exposure.CollidesWithADeclaration(r.imp().module(), r.name());
        };
    }

    /**
     * {@code module} with the import lines its declarations do not need left out. A module's
     * {@code let} bodies are not published, so an import only they used would otherwise be
     * republished and every importing project would have to put that module on its path to read
     * declarations that never mention it (issue #138).
     *
     * <p>Needed is decided on the words of the published text rather than on the parsed
     * declarations. The text is exactly what an importing project reads, and a word is a word
     * wherever it is written — in a field's type, a spread, an invariant, a helper an invariant
     * calls, an exposed composition's output. A walk over the parsed forms would have to name every
     * place a type can appear and would drop an import the day one is added; a word that is written
     * nowhere cannot be referred to by anything.
     */
    private static Ast.Module withNeededImports(Ast.Module module, String declared) {
        Set<String> written = new LinkedHashSet<>();
        Set<String> qualifiers = new LinkedHashSet<>();
        for (String word : words(declared)) {
            written.add(word);
            int dot = word.lastIndexOf('.');
            if (dot > 0) {
                qualifiers.add(word.substring(0, dot));
            }
        }
        List<Ast.Import> needed = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Collections.disjoint(written, imp.names())
                    || qualifiers.contains(imp.module())
                    || (imp.alias() != null && qualifiers.contains(imp.alias()))) {
                needed.add(imp);
            }
        }
        if (needed.size() == module.imports().size()) {
            return module;
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(), needed,
                module.defs(), module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    /**
     * Every maximal run of name characters in {@code text}, a qualified name counting as one word.
     * The dot joins a qualifier to what it qualifies, so it is part of a run; a dot that does not
     * join two names is dropped from the ends, which is what makes the spread {@code ...Common}
     * read as the name it spreads.
     *
     * <p>A run inside a string literal is a word here too: it costs an import that is kept, which is
     * what was published anyway.
     */
    private static List<String> words(String text) {
        List<String> words = new ArrayList<>();
        int start = -1;
        for (int i = 0; i <= text.length(); i++) {
            boolean part = i < text.length()
                    && (Character.isLetterOrDigit(text.charAt(i)) || text.charAt(i) == '_'
                            || text.charAt(i) == '.');
            if (part && start < 0) {
                start = i;
            } else if (!part && start >= 0) {
                String word = trimDots(text.substring(start, i));
                if (!word.isEmpty()) {
                    words.add(word);
                }
                start = -1;
            }
        }
        return words;
    }

    private static String trimDots(String word) {
        int from = 0;
        int to = word.length();
        while (from < to && word.charAt(from) == '.') {
            from++;
        }
        while (to > from && word.charAt(to - 1) == '.') {
            to--;
        }
        return word.substring(from, to);
    }

    /** The class a module's declarations are stamped on. */
    private static String declarationsClassOf(String module) {
        return SoutherJvmAbi.nameOf(new GeneratedClass.ModuleDeclarations(module)).binaryName();
    }
}
