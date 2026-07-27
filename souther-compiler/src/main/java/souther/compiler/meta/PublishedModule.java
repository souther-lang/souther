package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.frontend.CstFrontend;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A module read back from what {@link ModuleMetadata} wrote into its classes: the declarations
 * another project needs in order to {@code import} it, without its {@code .sou}.
 *
 * <p>The declarations are put back together as one source and handed to the parser, so what an
 * importing project sees is what the declaring project wrote, read by the same front end. Nothing
 * about the module's implementation comes back — its {@code let} bodies were never published — with
 * one exception: a helper an invariant calls, because the invariant cannot be read without it.
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
        if (m.compat() != Backend.BOUNDARY_VERSION) {
            throw incompatible(m);
        }
        StringBuilder source = new StringBuilder(m.header()).append('\n');
        for (String line : m.imports()) {
            source.append(line).append('\n');
        }
        Set<String> injected = new LinkedHashSet<>();
        for (String type : m.types()) {
            source.append('\n').append(declaration(classes, m, type, moduleName + "." + type,
                    Declarations::data)).append('\n');
        }
        for (String behavior : m.behaviors()) {
            String binaryName = moduleName + "." + Backend.behaviorClass(behavior);
            source.append('\n')
                    .append(declaration(classes, m, behavior, binaryName,
                            Declarations::behaviorSignature))
                    .append('\n');
            if (Boolean.TRUE.equals(classes.of(binaryName).behaviorInjected())) {
                injected.add(behavior);
            }
        }
        for (String helper : m.invariantHelpers()) {
            source.append('\n').append(helper).append('\n');
        }
        return new PublishedModule(CstFrontend.parse(source.toString(), null), injected);
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
