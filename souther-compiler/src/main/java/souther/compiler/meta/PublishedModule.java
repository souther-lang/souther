package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.frontend.CstFrontend;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A module read back from what {@link ModuleMetadata} wrote into its classes: the declarations
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
 * <p>{@code injected} does not survive as source. A behavior is an injection target when its module
 * writes no {@code let} for it, and no {@code let} came back for any of them, so the flag that was
 * published is carried here beside the module rather than inferred from it.
 */
public record PublishedModule(Ast.Module module, Set<String> injectedBehaviors) {

    /** Where the annotations of one compiled module are read from — a jar on the classpath, the
     * classes of a compile in progress. A name it does not know is {@code null}. */
    public interface Classes {

        /** The declarations on {@code binaryName}'s class, or null if there is no such class. */
        Declarations of(String binaryName);
    }

    /** What one class was annotated with. A class carries at most one of each. */
    public record Declarations(SoutherModuleView module, String data, String behaviorSignature,
                               Boolean behaviorInjected) {}

    /** The {@code $Module} annotation's members. */
    public record SoutherModuleView(int compat, String compiler, String name, String header,
                                    List<String> imports, List<String> types,
                                    List<String> behaviors, List<String> invariantHelpers) {}

    /**
     * The module named {@code moduleName}, or null when {@code classes} has no {@code $Module} for
     * it — the name is not a compiled Souther module, or is one from before modules carried their
     * declarations.
     */
    public static PublishedModule read(String moduleName, Classes classes) {
        Declarations found = classes.of(Backend.moduleClassName(moduleName));
        if (found == null || found.module() == null) {
            return null;
        }
        SoutherModuleView m = found.module();
        // A member this compiler asks for and the writer did not write reads as its default. The
        // header is the one that cannot be defaulted — without it there is no module to parse — so a
        // module that carries none was written by something this compiler does not agree with,
        // whatever its number says.
        if (m.compat() != Backend.BOUNDARY_VERSION || m.header().isBlank()) {
            throw incompatible(m);
        }
        StringBuilder declarations = new StringBuilder();
        Set<String> injected = new LinkedHashSet<>();
        for (String type : m.types()) {
            declarations.append('\n').append(declaration(classes, m, type, moduleName + "." + type,
                    Declarations::data)).append('\n');
        }
        for (String behavior : m.behaviors()) {
            String binaryName = moduleName + "." + Backend.behaviorClass(behavior);
            declarations.append('\n')
                    .append(declaration(classes, m, behavior, binaryName,
                            Declarations::behaviorSignature))
                    .append('\n');
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
        Ast.Module module = CstFrontend.parse(source.toString(), null);
        // Which imports are needed is asked of the header and the declarations — everything that was
        // published except the import lines themselves.
        return new PublishedModule(
                withNeededImports(module, m.header() + "\n" + declarations), injected);
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
                module.defs(), module.behaviors(), module.fns(), module.examples(), module.fakes(),
                module.exampleFileTarget(), module.pos());
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

    private static String declaration(Classes classes, SoutherModuleView m, String name,
                                      String binaryName,
                                      java.util.function.Function<Declarations, String> member) {
        Declarations found = classes.of(binaryName);
        String text = found == null ? null : member.apply(found);
        if (text == null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.module.publishedincomplete").title("check.module.title")
                            .args(name, m.name()).hint("check.module.publishedincomplete.hint", m.name())
                            .build(),
                    "module `" + m.name() + "` says it declares `" + name
                            + "`, but the class carrying that declaration is not on the classpath");
        }
        return text;
    }

    private static CompileException incompatible(SoutherModuleView m) {
        return CompileException.of(
                Diagnostic.of(null, "check.module.incompatible").title("check.module.title")
                        .args(m.name(), m.compiler())
                        .hint("check.module.incompatible.hint", m.name()).build(),
                "module `" + m.name() + "` was compiled by Souther " + m.compiler()
                        + ", which does not agree with this compiler about what an importing module"
                        + " may reach; rebuild it with this compiler");
    }
}
