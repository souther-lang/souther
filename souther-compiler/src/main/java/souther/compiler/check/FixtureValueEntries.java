package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The definitions a module emits so that a fixture can read one of the values a row or fake actually
 * names by running the value's own generated code, rather than interpreting the value's body a second
 * time.
 *
 * <p>One per value a row or fake names bare, that has no entry already: nullary, its body the exact
 * reference the fixture wrote and nothing else, minted and read for the same reason {@link
 * ValueEntries} is. Where the module already publishes the value, its {@link ValueEntries#methodFor
 * published entry} is reused instead of minting a second one — a fixture and another module are two
 * callers of one address, not two entries answering the one question.
 *
 * <p>{@link #referencedValues} finds which values those are by walking the same written text {@link
 * RowFixtures#placed} numbers, in exactly the forms {@code FixtureReader.raw} reads a fixture in — a
 * literal's parts, a construction's fields and spreads, a collection's elements, a {@code let}'s value
 * and body. Not a callee an application applies, which is a different question a fixture never asks by
 * name. Not every value the module happens to declare, either: which values a search composing a
 * further row may still ask for by name, among those no row here mentions, is a wider question this
 * does not answer, and {@code FixtureReader} still reads such a value by its template where this finds
 * it no entry.
 *
 * <p>An entry's body decides nothing about how the value it names runs: {@link HelperInliner#materialise}
 * reads that reference the same way it reads any other, and chooses a method call, a folded constant,
 * or a call into the module that declares the value, without this class or {@link
 * souther.compiler.examples.FixtureReader} having to know which.
 */
public final class FixtureValueEntries {

    private FixtureValueEntries() {
    }

    /** The name the fixture entry of {@code value} is emitted under. Written nowhere a source could
     *  spell, and never the same as {@link ValueEntries#methodFor} — the two are minted for disjoint
     *  values, since a published value's fixture entry is its published one, reused rather than
     *  duplicated. */
    public static String methodFor(String value) {
        return "$fixture.value." + value;
    }

    /**
     * The values a row or fake names bare, each held as the reference it was named through — reused
     * as the entry's own body, so the entry reaches the value exactly as the fixture resolved it (its
     * own module for a local value, the declaring module for an imported one) rather than this
     * guessing which of the two a fresh reference would have to say.
     *
     * <p>{@code placed} is {@link RowFixtures#placed}'s own answer, handed in rather than asked for
     * here: {@link RowFixtures#emitted} already walks it once for the same module, and a second
     * walk here would be the second order {@code placed}'s own doc refuses. A name found among these
     * operands is a name some row or fake actually wrote — never a name a value's own body happens to
     * reach, which lowering resolves on its own once an entry exists for the value naming it. A name
     * written more than once keeps its first reference; every one denotes the same value, so one
     * entry answers all of them.
     */
    static Map<ValueName.Helper, Hir.Var.Denoting> referencedValues(List<RowFixtures.Placed> placed) {
        Map<ValueName.Helper, Hir.Var.Denoting> out = new LinkedHashMap<>();
        for (RowFixtures.Placed each : placed) {
            collect(each.operand(), out);
        }
        return out;
    }

    /**
     * {@code e}'s value references, in exactly the forms {@code FixtureReader.raw} descends into: a
     * literal has none, a negation and a fold read their operands, a construction reads its spreads
     * and its fields, a collection reads its elements, an application reads its arguments and never
     * the callee it applies, and a {@code let} reads its value and its body.
     */
    private static void collect(Hir.Expr e, Map<ValueName.Helper, Hir.Var.Denoting> out) {
        if (e instanceof Hir.Var.Denoting v && v.denotes() instanceof ValueName.Helper helper) {
            out.putIfAbsent(helper, v);
        } else if (e instanceof Hir.Neg n) {
            collect(n.operand(), out);
        } else if (e instanceof Hir.Binary b) {
            collect(b.left(), out);
            collect(b.right(), out);
        } else if (e instanceof Hir.Apply c) {
            for (Hir.Expr arg : c.args()) {
                collect(arg, out);
            }
        } else if (e instanceof Hir.LetIn let) {
            collect(let.value(), out);
            collect(let.body(), out);
        } else if (e instanceof Hir.NewData nd) {
            for (Hir.Var spread : nd.spreads()) {
                collect(spread, out);
            }
            for (Hir.FieldInit fi : nd.inits()) {
                collect(fi.value(), out);
            }
        } else if (e instanceof Hir.ListLit l) {
            for (Hir.Expr element : l.elements()) {
                collect(element, out);
            }
        } else if (e instanceof Hir.Tuple t) {
            for (Hir.Expr element : t.elements()) {
                collect(element, out);
            }
        }
        // A literal, and anything else a fixture may write, names no value.
    }

    /**
     * {@code defs} is what this compilation mints — a fixture entry for a value with no published
     * one. {@code methods} is every value a row or fake names bare, mint and reuse alike, by the
     * declaration it is: what {@link souther.compiler.examples.FixtureReader} reads, so the address a
     * name resolves to is decided once, here, and never read off a name a second time.
     */
    public record Emitted(Map<String, Hir.FnDef> defs, Map<ValueName.Helper, String> methods) {
    }

    /** The fixture entries {@code surface}'s rows and fakes need, and the correspondence a fixture
     *  reads a named value's method through. {@code placed} is {@link RowFixtures#placed}'s answer
     *  for the same module, shared rather than recomputed. */
    public static Emitted emitted(CheckSurface surface, DeclarationNewtypes newtypes,
                                  List<RowFixtures.Placed> placed) {
        Hir.Module module = surface.module();
        Set<String> published = ValueEntries.publishedValues(module);
        Map<String, Hir.FnDef> defs = new LinkedHashMap<>();
        Map<ValueName.Helper, String> methods = new LinkedHashMap<>();
        for (Map.Entry<ValueName.Helper, Hir.Var.Denoting> named
                : referencedValues(placed).entrySet()) {
            ValueName.Helper of = named.getKey();
            if (of.module().equals(module.name()) && published.contains(of.name())) {
                methods.put(of, ValueEntries.methodFor(of.name()));
                continue;
            }
            Hir.Var.Denoting reference = named.getValue();
            String name = methodFor(of.module() + "." + of.name());
            Hir.FnDef entry = new Hir.FnDef(WrittenName.synthetic(name, reference.pos()),
                    module.name(), List.of(), null, new Hir.FnBody.Written(reference),
                    new Hir.Modifiers(true, true), new DefinitionRole.FixtureValueEntry(of),
                    reference.pos());
            defs.put(name, Desugared.Fn.desugar(entry, newtypes).read());
            methods.put(of, name);
        }
        return new Emitted(defs, methods);
    }
}
