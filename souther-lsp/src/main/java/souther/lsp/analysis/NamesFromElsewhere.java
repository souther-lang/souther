package souther.lsp.analysis;

import souther.compiler.ast.Hir;
import souther.compiler.check.Scoping;
import souther.compiler.check.Symbols;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Names;
import souther.compiler.types.ValueName;
import souther.lsp.protocol.CompletionItem;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a document may write that it does not declare itself, as the compiler last answered it.
 *
 * <p>Which bare spelling reaches what is the compiler's, and both namespaces are asked of it every
 * time it can answer: {@link Names.NameScope} for the declarations a name reaches, which carry what
 * kind of declaration each is, and {@link Names.ModuleScope} for the value namespace. Nothing here
 * reads an import line. What one brings in is {@code Scoping}'s to say, and a second reader of those
 * lines would be that rule written twice, to go out of agreement the first time either moved.
 *
 * <p>The compiler cannot answer about a module whose source will not parse — that file is held out
 * of the compile, which is exactly the file being typed in — and what is kept here is the last
 * answer it gave, so an editor goes on offering names while the compiler has nothing to say about
 * the file in front of the author.
 *
 * <p>An availability fallback and not a second source of names. It is written only where the
 * compiler answered and read only where it did not; the two are never merged, so a name that is
 * offered is either what the current compile says or what the last one did, and deleting an import
 * from a document that parses takes its names away at once.
 *
 * <p>Kept per document rather than per module, because a module is not one file. Seen from an
 * attached {@code examples for} file, the declarations of its module's own source are from
 * elsewhere — that document does not declare them and cannot read them off its own text — and a
 * partition drawn at the module would drop exactly those while the other file is the one being
 * edited. What is from elsewhere is settled against the spellings the document itself declares,
 * which is exact: one spelling reaches one thing in a scope.
 */
final class NamesFromElsewhere {

    /** Document URI → what the last compile that could answer said reaches it from elsewhere. */
    private final Map<String, List<CompletionItem>> byDocument = new LinkedHashMap<>();

    /**
     * The candidates {@code uri} reaches from outside itself.
     *
     * <p>{@code declaredHere} is what the document's own text declares, read from its syntax tree.
     * Those are the document's to answer for, every time, so that a definition being written now is
     * offered before it compiles; they are kept out of what is remembered rather than filtered on
     * the way out, so a name deleted while the file will not parse does not come back.
     */
    List<CompletionItem> of(Compilation compilation, String uri, String module,
                            Set<String> declaredHere) {
        List<CompletionItem> answered = ask(compilation, module, declaredHere);
        if (answered == null) {
            return byDocument.getOrDefault(uri, List.of());
        }
        byDocument.put(uri, answered);
        return answered;
    }

    /**
     * What the compile says reaches this document from elsewhere, or null where it cannot say.
     *
     * <p>Null for a document whose module cannot be named as well as for one whose module the
     * compile does not have. Which module an attached {@code examples for} file belongs to is the
     * compile's answer — its text declares no module of its own — so a file held out of the compile
     * for its own syntax errors, or one whose module's other source was, has no module to be asked
     * about. That is the same absence and takes the same answer.
     */
    private static List<CompletionItem> ask(Compilation compilation, String module,
                                            Set<String> declaredHere) {
        if (module == null) {
            return null;
        }
        Answer<Symbols> types = compilation.db().ask(new Names.NameScope(module));
        Answer<Scoping.Scoped> scope = compilation.db().ask(new Names.ModuleScope(module));
        if (!types.present() || !scope.present()) {
            return null;
        }
        List<CompletionItem> found = new ArrayList<>();
        // The type namespace first, as a bare name in a value position is answered: a data written
        // as a value is its construction, and the value table is read after that.
        types.value().reachable().forEach((spelling, def) -> {
            if (!declaredHere.contains(spelling)) {
                found.add(new CompletionItem(spelling, kindOf(def), def.declaredIn()));
            }
        });
        scope.value().reachable().byName().forEach((spelling, name) -> {
            CompletionItem item = itemOf(spelling, name);
            if (item != null && !declaredHere.contains(spelling)) {
                found.add(item);
            }
        });
        return List.copyOf(found);
    }

    /** Forgets every document the workspace no longer holds, so a file that was deleted or renamed
     * leaves no names behind. */
    void forgetAllBut(Collection<String> uris) {
        byDocument.keySet().retainAll(Set.copyOf(uris));
    }

    /** What kind of declaration an editor is being offered. Read off the declaration, so a sum is
     * not offered as a product because the two are both {@code data}. */
    private static int kindOf(Hir.Def def) {
        return switch (def) {
            case Hir.SumData _ -> CompletionItem.ENUM;
            case Hir.Data _, Hir.UnitData _ -> CompletionItem.CLASS;
        };
    }

    /**
     * One value-namespace candidate, or null where the spelling names nothing to offer.
     *
     * <p>A library namespace applied ({@code Date} in {@code Date(...)}) is not a member of
     * anything, and a local is not reachable from a table — the bindings in force at the cursor are
     * the document's to read.
     */
    private static CompletionItem itemOf(String spelling, ValueName name) {
        return switch (name) {
            case ValueName.Behavior behavior ->
                    new CompletionItem(spelling, CompletionItem.INTERFACE, behavior.module());
            case ValueName.Helper helper ->
                    new CompletionItem(spelling, CompletionItem.FUNCTION, helper.module());
            case ValueName.Stdlib stdlib when !stdlib.isNamespace() ->
                    new CompletionItem(spelling, CompletionItem.FUNCTION, stdlib.alias());
            default -> null;
        };
    }
}
