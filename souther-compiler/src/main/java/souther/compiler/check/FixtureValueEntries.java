package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
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
 * it one. Not every value the module happens to declare, either — {@code typed}, below, is the
 * answer to which further ones: {@link TypedFixtureValues} finds a value a search composing a
 * further row may ask for by name before any row here names it, and this mints for those too, so
 * {@code FixtureReader} never falls back to reading a value by its own written body a second time.
 *
 * <p>{@link #bareValueReference} is the one place this question is asked, so that a reader of it and
 * this do not keep two copies of the same predicate to drift apart. {@link
 * souther.compiler.query.Adequacy}'s search reads a row's own input by it too, when deciding which
 * value to reuse as a baseline for a further row — the invariant that reading rests on is one
 * direction only: a name the search treats as a baseline is a name this mints an entry for, since
 * {@link RowFixtures#placed} is wider than a row's own inputs (it numbers a {@code with}, an
 * expected value and a fake's occurrences too), and this mints for every position among them, not
 * only the ones the search happens to read as an origin.
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

    /** Nowhere a source wrote: the position a candidate {@link TypedFixtureValues} discovers is
     *  minted under, since no row or fake wrote a reference for this to reuse the position of. */
    private static final SourcePos DISCOVERED = new SourcePos(0, 0);

    /** The fixture entries {@code surface}'s rows and fakes need, and the correspondence a fixture
     *  reads a named value's method through. {@code placed} is {@link RowFixtures#placed}'s answer
     *  for the same module, shared rather than recomputed. {@code typed} is {@link
     *  TypedFixtureValues#of}'s answer for the same module: a candidate a search may offer as a
     *  baseline before any row names it, minted here so that {@code FixtureReader} finds an entry
     *  already made for it rather than falling back to interpreting its body. A value both a row
     *  names and {@code typed} states keeps the row's own reference — reused, never minted twice.
     */
    public static Emitted emitted(CheckSurface surface, DeclarationNewtypes newtypes,
                                  List<RowFixtures.Placed> placed,
                                  Map<Type, List<ReachName.Declaration>> typed) {
        Hir.Module module = surface.module();
        Set<String> published = ValueEntries.publishedValues(module);
        Map<String, Hir.FnDef> defs = new LinkedHashMap<>();
        Map<ValueName.Helper, String> methods = new LinkedHashMap<>();
        for (Map.Entry<ValueName.Helper, Hir.Var.Denoting> named
                : referencedValues(placed).entrySet()) {
            mint(defs, methods, module, newtypes, published, named.getKey(), named.getValue());
        }
        for (List<ReachName.Declaration> candidates : typed.values()) {
            for (ReachName.Declaration candidate : candidates) {
                ValueName.Helper of = (ValueName.Helper) candidate.denotes();
                if (methods.containsKey(of)) {
                    continue;
                }
                Hir.Var.Denoting reference = (Hir.Var.Denoting) Hir.Var.respelled(
                        candidate.rendered(), candidate, new FixtureReferenceOrigin(0), DISCOVERED,
                        null);
                mint(defs, methods, module, newtypes, published, of, reference);
            }
        }
        return new Emitted(defs, methods);
    }

    /** Mints the entry {@code of} is read through, or reuses its published one where the module
     *  already publishes it — one decision, made the same way whether a row named {@code reference}
     *  or {@link TypedFixtureValues} discovered it. */
    private static void mint(Map<String, Hir.FnDef> defs, Map<ValueName.Helper, String> methods,
                             Hir.Module module, DeclarationNewtypes newtypes, Set<String> published,
                             ValueName.Helper of, Hir.Var.Denoting reference) {
        if (of.module().equals(module.name()) && published.contains(of.name())) {
            methods.put(of, ValueEntries.methodFor(of.name()));
            return;
        }
        String name = methodFor(of.module() + "." + of.name());
        Hir.FnDef entry = new Hir.FnDef(WrittenName.synthetic(name, reference.pos()),
                module.name(), List.of(), null, new Hir.FnBody.Written(reference),
                new Hir.Modifiers(true, true), new DefinitionRole.FixtureValueEntry(of),
                reference.pos());
        defs.put(name, Desugared.Fn.desugar(entry, newtypes).read());
        methods.put(of, name);
    }
}
