package souther.compiler.frontend;

import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Declares the unit data a module only names. A name written where a module introduces a type — a
 * sum's case list, a behavior's output, a composition's declared output — and declared nowhere is a
 * data with no fields, and the name alone is its declaration (spec §unit-data). Without this,
 * {@code data Terms = Net15 | Net30} needed a {@code data Net15} line that repeated the name and
 * said nothing else.
 *
 * <p>Everywhere else a type is referred to, not introduced: a parameter type, a field's type,
 * {@code constructs}, {@code depends on}, a match arm, a decoder variant. A name unknown there is
 * still unknown, and reported as before.
 *
 * <p>Whether a name is declared is answered inside the module: its own definitions and the names its
 * imports list. A sum's case is module-local anyway (E1606), so nothing on the class path can
 * change the answer. A qualified name ({@code inventory.在庫不足}) refers to another module by
 * writing it, so it is never introduced here.
 */
public final class ImplicitUnits {

    private ImplicitUnits() {
    }

    /** Names that mean something without a declaration: the primitives and library namespaces, the
     * runtime's arithmetic failure cases, and Option's two cases (which a module may not declare).
     * The namespaces come from {@link Reserved} — the language's constant — rather than from
     * {@code Prelude}, whose loading parses sources back through {@link #expand} and so must not
     * be what this class initializes against. */
    private static final Set<String> BUILT_IN = builtIn();

    private static Set<String> builtIn() {
        Set<String> names = new HashSet<>(Reserved.QUALIFIERS);
        names.add("Raw");
        names.add("DivisionByZero");
        names.add("NotANumber");
        names.add("NotADate");
        names.add("NotATime");
        names.add("Some");
        names.add("None");
        return Set.copyOf(names);
    }

    /** {@code module} with a unit data added for each name it introduces and does not declare. */
    public static Ast.Module expand(Ast.Module module) {
        Set<String> declared = new HashSet<>();
        for (Ast.Def def : module.defs()) {
            declared.add(def.name());
        }
        for (Ast.Import imp : module.imports()) {
            declared.addAll(imp.names());
        }

        Map<String, Ast.UnitData> added = new LinkedHashMap<>();
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.SumData sum) {
                for (Ast.Name caseName : sum.cases()) {
                    introduce(caseName.written(), caseName.pos(), module.name(), declared,
                            added);
                }
            }
        }
        for (Ast.BehaviorDef behavior : module.behaviors()) {
            switch (behavior) {
                case Ast.SpecBehavior spec ->
                        introduceAll(spec.ret(), module.name(), declared, added);
                case Ast.PipeBehavior pipe ->
                        introduceAll(pipe.declaredOut(), module.name(), declared, added);
            }
        }
        for (Ast.RetType output : module.exposedOutputs().values()) {
            introduceAll(output, module.name(), declared, added);
        }

        if (added.isEmpty()) {
            return module;
        }
        List<Ast.Def> defs = new ArrayList<>(module.defs());
        defs.addAll(added.values());
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                module.imports(), defs, module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    private static void introduceAll(Ast.RetType output, String declaredIn, Set<String> declared,
                                     Map<String, Ast.UnitData> added) {
        if (output == null) {
            return;
        }
        for (Ast.TypeTerm term : output.cases()) {
            if (term instanceof Ast.TypeRef ref
                    && ref.arg() == null && ref.tupleElems() == null) {
                introduce(ref.name(), ref.pos(), declaredIn, declared, added);
            }
        }
    }

    private static void introduce(String name, SourcePos pos, String declaredIn,
                                  Set<String> declared, Map<String, Ast.UnitData> added) {
        if (declared.contains(name) || added.containsKey(name)
                || name.indexOf('.') >= 0                  // qualified: another module declares it
                || name.startsWith("'")                    // a type variable, written in the core
                || BUILT_IN.contains(name)) {
            return;
        }
        // No name position: nobody wrote this declaration. The place `pos` names is the reference
        // that implied it, and reading a use as a declaration's name would answer a cursor there
        // about a declaration that is not in the file.
        added.put(name, new Ast.UnitData(name, declaredIn, pos));
    }
}
