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
 * RowFixtures#placed} numbers, and it asks of each operand exactly {@link #bareValueReference}'s
 * question: is the whole of it nothing but a name denoting a value. An argument a computed operand
 * hands a helper is not this — {@code applyTo(inc, 1)} names no value by this reading, it is a row's
 * own operand and runs as generated code already — and a private value that stood at one, being
 * one nothing outside its own module ever reaches, has no type to write for a caller nothing gives
 * it one. Not every value the module happens to declare, either: which values a search composing a
 * further row may still ask for by name, among those no row here names this way, is a wider question
 * this does not answer, and {@code FixtureReader} still reads such a value by its template where this
 * finds it no entry.
 *
 * <p>{@link #bareValueReference} is the one place this question is asked. {@link
 * souther.compiler.query.Adequacy}'s search reads a row's own baseline by the same question, over
 * the same operands, so a name this mints no entry for is a name the search does not read as a
 * baseline either — two readers of one operand answering from one predicate rather than each
 * keeping a copy of it to drift out of step with the other's.
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
     * Whether {@code e} is nothing but a bare name denoting a value — never a construction built
     * from one, an argument or a field holding one, or a spread copying one. The value denoted, or
     * null where {@code e} is any other form or denotes anything else.
     *
     * <p>Shallow, and deliberately so: a value inside a larger operand is not named by this reading,
     * it is computed by the operand — {@code applyTo(inc, 1)} runs {@code inc} as generated code
     * already, through {@code inc}'s own compiled representation, the same as any other name a row's
     * operand reaches. Reading past the top would find it anyway and mint an entry nothing calls, for
     * a value that may hold a function an entry cannot be given one of without a type nothing else
     * asks it to have (spec §a-function-bindings-type-is-known).
     */
    public static Hir.Var.Denoting bareValueReference(Hir.Expr e) {
        return e instanceof Hir.Var.Denoting v && v.denotes() instanceof ValueName.Helper ? v : null;
    }

    /**
     * The values a row or fake names bare, each held as the reference it was named through — reused
     * as the entry's own body, so the entry reaches the value exactly as the fixture resolved it (its
     * own module for a local value, the declaring module for an imported one) rather than this
     * guessing which of the two a fresh reference would have to say.
     *
     * <p>{@code placed} is {@link RowFixtures#placed}'s own answer, handed in rather than asked for
     * here: {@link RowFixtures#emitted} already walks it once for the same module, and a second
     * walk here would be the second order {@code placed}'s own doc refuses. A name written more than
     * once keeps its first reference; every one denotes the same value, so one entry answers all of
     * them.
     */
    static Map<ValueName.Helper, Hir.Var.Denoting> referencedValues(List<RowFixtures.Placed> placed) {
        Map<ValueName.Helper, Hir.Var.Denoting> out = new LinkedHashMap<>();
        for (RowFixtures.Placed each : placed) {
            Hir.Var.Denoting v = bareValueReference(each.operand());
            if (v != null) {
                out.putIfAbsent((ValueName.Helper) v.denotes(), v);
            }
        }
        return out;
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
