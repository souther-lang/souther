package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.check.Exposing;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

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
 * converts is stated rather than decided by how wide a caller's catch happened to be. The one catch
 * left is around the parse, and it is around the parse alone.
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
        PublishedClasses.Declarations found = declarationsOf(module, classes);
        return found != null && found.module() != null;
    }

    /** What {@code classes} carry for {@code moduleName}. */
    public static Readback read(String moduleName, PublishedClasses classes) {
        PublishedClasses.Declarations found = declarationsOf(moduleName, classes);
        if (found == null || found.module() == null) {
            return new Readback.SaysNothing();
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
            String text = declared(classes, moduleName + "." + type,
                    PublishedClasses.Declarations::data);
            if (text == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(type));
            }
            declarations.append('\n').append(text).append('\n');
        }
        for (String behavior : m.behaviors()) {
            String binaryName = SoutherJvmAbi.nameOf(
                    new GeneratedClass.BehaviorInterface(moduleName, behavior)).binaryName();
            String text = declared(classes, binaryName,
                    PublishedClasses.Declarations::behaviorSignature);
            if (text == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(behavior));
            }
            declarations.append('\n').append(text).append('\n');
            if (Boolean.TRUE.equals(classes.of(binaryName).behaviorInjected())) {
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
        // Which imports are needed is asked of the header and the declarations — everything that was
        // published except the import lines themselves.
        Exposing.Checked checked =
                Exposing.check(withNeededImports(parsed, m.header() + "\n" + declarations));
        if (!checked.refused().isEmpty()) {
            return unreadable(moduleName, new Readback.Failure.InvalidExposure(checked.refused()));
        }
        return new Readback.Ready(
                new ReadableModule(checked.module(), injected, checked.exposed()));
    }

    private static Readback unreadable(String module, Readback.Failure why) {
        return new Readback.Unreadable(module, why);
    }

    /** What {@code classes} carry on {@code module}'s declarations class, or null where there is no
     *  such class. Asked one way, so that {@link #carry} and {@link #read} cannot come to differ
     *  about whether the path has a name. */
    private static PublishedClasses.Declarations declarationsOf(String module,
                                                                PublishedClasses classes) {
        return classes.of(
                SoutherJvmAbi.nameOf(new GeneratedClass.ModuleDeclarations(module)).binaryName());
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

    /** The text {@code member} reads off {@code binaryName}'s class, or null where these classes do
     *  not carry it. */
    private static String declared(PublishedClasses classes, String binaryName,
                                   Function<PublishedClasses.Declarations, String> member) {
        PublishedClasses.Declarations found = classes.of(binaryName);
        return found == null ? null : member.apply(found);
    }
}
