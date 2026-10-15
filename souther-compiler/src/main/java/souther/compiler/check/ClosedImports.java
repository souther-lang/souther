package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What the modules one module imports publish to it, each definition closed by the module that
 * declares it, and the policy that closing expanded under.
 *
 * <p>The policy travels with the definitions because it is what they are a representation of. A
 * published body is expanded where it was written, before any reader sees it, so a reader cannot
 * expand it again under another policy: closed under {@link InliningPolicy#FULL}, a call to
 * {@code List.drop} is already the body of {@code List.drop}, and a table that leaves the language's
 * operations standing would hold that body as if the importer's author had written it. So a table
 * takes these only under the policy they were closed under ({@link HelperTable#of}).
 *
 * @param policy      what each body here was expanded under where it was written
 * @param definitions each definition under the qualified name a reader reaches it by, in the order
 *                    they were handed over
 */
public record ClosedImports(InliningPolicy policy, Map<String, Hir.FnDef> definitions) {

    public ClosedImports {
        definitions = Collections.unmodifiableMap(new LinkedHashMap<>(definitions));
    }

    /** No definitions, for a module that imports nothing or whose imports could not be read. */
    public static ClosedImports none(InliningPolicy policy) {
        return new ClosedImports(policy, Map.of());
    }
}
