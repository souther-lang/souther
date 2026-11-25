package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SourceLayout;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModulePath;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every name a model that compiles writes is answered by the compiler — asked of the place it is
 * written, what it denotes — unless the place names no declaration at all.
 *
 * <p>What an editor stands on. It takes the compiler's answer about a name as final wherever the
 * compile read the document, and goes nowhere where the compiler says nothing, so a name the
 * compile reads and keeps no answer for is a name an editor cannot follow, show or rename. An
 * {@code example}'s target was one, and so were the entries of an import or {@code exposing} list;
 * a form added without an answer for the names it writes is found here rather than by an author
 * whose rename left it behind.
 *
 * <p>The places that name no declaration are a set this test closes: a module's own name, the alias
 * an import gives one, a field — declared, given a value, or read off a value — and a container the
 * language shapes out of the types it is applied to ({@code List<Int>}), which is a shape and not a
 * declaration. Nothing else in a model that compiles is a name with no answer; a primitive is the
 * language's declaration and is answered as one.
 */
class EveryNameACompilingModelWritesIsAnsweredTest {

    private static final String LIB = """
            module lib exposing ( Amount, scaled )

            data Amount = { value: Int }

            let scaled (a: Amount, by: Int): Amount = Amount { value = a.value * by }
            """;

    private static final String MODEL = """
            module m exposing ( Order, Decision, price, decide, said )

            import lib as l ( Amount, scaled )

            data Order = { qty: Int, unit: l.Amount }

            data Accepted = { qty: Int }

            data Rejected = { qty: Int }

            data Decision = Accepted | Rejected

            data Count = Int

            behavior rate : (o: Order) -> Int

            behavior tax : (o: Order) -> Int

            behavior price : (o: Order) -> Amount
                depends on rate, tax

            let price (o, rate, tax) = scaled(o.unit, rate(o) + tax(o))

            behavior decide : (o: Order) -> Decision
                constructs Accepted, Rejected, Count

            let decide (o) = {
                let n = Count(o.qty)
                if count(n) > 0 then Accepted { qty = o.qty } else Rejected { qty = o.qty }
            }

            let count (Count(c)) = c

            behavior said : (d: Decision) -> String

            let said (d) = match d with
                | Accepted -> "yes"
                | Rejected -> "no"

            behavior decided = decide >-> said

            let total (xs: List<Int>): Int = List.sum(xs)
            """;

    private static final String ATTACHED = """
            examples for m

            let sample = Order { qty = 2, unit = Amount { value = 3 } }

            fake rate
                | _ -> 2

            example price
                | (sample) with tax = 1 -> Amount { value = 9 }

            example decide
                | (sample) -> Accepted { qty = 2 }
            """;

    private static final Map<String, String> TEXTS = texts();

    private static Map<String, String> texts() {
        Map<String, String> out = new LinkedHashMap<>();
        out.put("lib.sou", LIB);
        out.put("m.sou", MODEL);
        out.put("m.examples.sou", ATTACHED);
        return out;
    }

    /** Whether {@code name} is written where no declaration is named: a module's name, an import's
     *  alias, a field, a container the language shapes out of the types it is applied to. */
    private static boolean namesNoDeclaration(SyntaxToken name) {
        SyntaxNode parent = name.parent();
        SyntaxKind holder = parent.parent() == null ? null : parent.parent().kind();
        return switch (parent.kind()) {
            case QUALIFIED_NAME -> holder == SyntaxKind.MODULE_HEADER
                    || holder == SyntaxKind.IMPORT_DECL || holder == SyntaxKind.EXAMPLES_FILE_HEADER;
            case IMPORT_ALIAS, FIELD, FIELD_INIT, FIELD_ACCESS, FIELD_GETTER -> true;
            case TYPE_REF -> parent.child(SyntaxKind.TYPE_ARGS).isPresent();
            default -> false;
        };
    }

    @Test
    void everyNameIsAnsweredOrNamesNoDeclaration() {
        Compilation compilation = ACompiledModel.compiles(
                Compilation.ofDocuments(TEXTS, Set.of(), ModulePath.EMPTY));

        List<String> unanswered = new ArrayList<>();
        TEXTS.forEach((file, text) -> {
            SourceLayout layout = compilation.db()
                    .ask(new Front.LayoutOf(new SourceId(file))).value();
            for (SyntaxToken name : names(CstParser.parse(text).root(), new ArrayList<>())) {
                SourcePos at = layout.placeAt(name.start());
                if (compilation.db().ask(new Names.TypeAt(at)).value() == null
                        && compilation.db().ask(new Names.ValueAt(at)).value() == null
                        && !namesNoDeclaration(name)) {
                    unanswered.add(file + ": `" + name.text() + "` in "
                            + name.parent().kind() + " at " + name.start());
                }
            }
        });

        assertEquals(List.of(), unanswered);
    }

    /** Every identifier under {@code node}, in the order written. */
    private static List<SyntaxToken> names(SyntaxNode node, List<SyntaxToken> into) {
        for (SyntaxElement each : node.children()) {
            if (each instanceof SyntaxNode child) {
                names(child, into);
            } else if (each instanceof SyntaxToken token && token.kind() == SyntaxKind.IDENT) {
                into.add(token);
            }
        }
        return into;
    }
}
