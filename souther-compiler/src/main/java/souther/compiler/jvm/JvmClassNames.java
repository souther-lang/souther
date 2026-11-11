package souther.compiler.jvm;

import souther.compiler.ast.Hir;
import souther.compiler.check.Boundary;
import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.SumCases;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Whether the classes a module is generated as keep to one class each: no two identities of the
 * module that the ABI spells as one JVM class.
 *
 * <p>Asked of the declarations and the signatures, before anything is written, so that a module
 * the JVM cannot hold is refused where the check says what is wrong with it and not only where the
 * classes are made. What collides is decided on the name {@link SoutherJvmAbi#nameOf} gives each
 * generated class, and what the report names is the Souther declarations that landed on it; the
 * mapping from an identity to a name is the ABI's and is not worked out again here.
 *
 * <p>Four ways to collide: a behavior's class with a data this module declares, with the class
 * another behavior capitalizes into (spec §jvm-behavior), a behavior's result union with either of
 * those, and a bridge case — the class a member of a union another module declared reaches the
 * union through — with any of them or with another bridge case.
 */
public final class JvmClassNames {

    private JvmClassNames() {}

    /**
     * Refuses {@code module} where two of the classes it is generated as are one.
     *
     * @param outputOf what the behavior of that name answers with, or null where it has no
     *                 signature
     * @throws CompileException naming the first pair that collide, in the order the module
     *                          declares them
     */
    public static void rejectCollisions(Hir.Module module, Function<String, Type> outputOf,
                                        DeclarationKinds kinds, SumCases sums) {
        Map<JvmClassName, Hir.Def> localTypes = new LinkedHashMap<>();
        for (Hir.Def d : module.defs()) {
            localTypes.put(SoutherJvmAbi.nameOf(new GeneratedClass.Value(d.declares())), d);
        }
        Map<JvmClassName, String> behaviorClassOwner = new LinkedHashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            JvmClassName cls = SoutherJvmAbi.nameOf(
                    new GeneratedClass.BehaviorInterface(module.name(), bd.name()));
            Hir.Def data = localTypes.get(cls);
            if (data != null) {
                throw CompileException.of(Diagnostic.at(bd.pos()).say(
                        new BehaviorMessage.ABehaviorCapitalizesOntoAData(bd.name(), data.name()))
                        .build());
            }
            String prev = behaviorClassOwner.put(cls, bd.name());
            if (prev != null) {
                throw CompileException.of(Diagnostic.at(bd.pos()).say(
                        new BehaviorMessage.TwoBehaviorsCapitalizeToOneClass(prev, bd.name(),
                                cls.classDesc().displayName())).build());
            }
        }
        Map<GeneratedClass.BehaviorResult, Type> results = new LinkedHashMap<>();
        for (Hir.BehaviorDef bd : module.behaviors()) {
            Type output = outputOf.apply(bd.name());
            if (output instanceof Type.Union) {
                results.put(new GeneratedClass.BehaviorResult(module.name(), bd.name()), output);
            }
        }
        rejectResultUnionCollisions(module, results.keySet(), localTypes, behaviorClassOwner);
        rejectBridgeCaseCollisions(module, results, kinds, sums, localTypes, behaviorClassOwner);
    }

    /**
     * A behavior with a union output is generated as a sealed interface named after it, so that
     * name is subject to the rule every other name this module emits is subject to. Two result
     * unions cannot collide with each other, their behaviors having already been refused for
     * capitalizing into one class.
     */
    private static void rejectResultUnionCollisions(
            Hir.Module module, Iterable<GeneratedClass.BehaviorResult> unions,
            Map<JvmClassName, Hir.Def> localTypes, Map<JvmClassName, String> behaviorClassOwner) {
        for (GeneratedClass.BehaviorResult union : unions) {
            JvmClassName cls = SoutherJvmAbi.nameOf(union);
            String resultName = cls.classDesc().displayName();
            Hir.BehaviorDef owner = behaviorNamed(module, union.behavior());
            if (localTypes.containsKey(cls)) {
                throw CompileException.of(Diagnostic.at(owner.pos())
                        .hint(new BehaviorMessage.AUnionOutputReachesJavaThroughThatName(resultName))
                        .say(new BehaviorMessage.AUnionOutputsInterfaceCollidesWithAData(
                                owner.name(), resultName)).build());
            }
            String behavior = behaviorClassOwner.get(cls);
            if (behavior != null) {
                throw CompileException.of(Diagnostic.at(owner.pos())
                        .hint(new BehaviorMessage.AUnionOutputReachesJavaThroughThatName(resultName))
                        .say(new BehaviorMessage.AUnionOutputsInterfaceCollidesWithABehavior(
                                owner.name(), resultName, behavior)).build());
            }
        }
    }

    /**
     * A member of a union that this module did not declare — a primitive, or a type another module
     * emitted — reaches the union through a bridge case this module emits (ADR-0057), a class
     * named after the member. Three ways to collide: with a data this module declares, with the
     * class a behavior capitalizes into, and with another bridge case, which is two members of one
     * spelling from two modules reaching here as members of two different unions of this module.
     */
    private static void rejectBridgeCaseCollisions(
            Hir.Module module, Map<GeneratedClass.BehaviorResult, Type> results,
            DeclarationKinds kinds, SumCases sums, Map<JvmClassName, Hir.Def> localTypes,
            Map<JvmClassName, String> behaviorClassOwner) {
        Map<TypeSymbol, List<GeneratedClass.BehaviorResult>> bridgeCases = new LinkedHashMap<>();
        results.forEach((union, output) -> {
            for (TypeSymbol member : Boundary.of(output, kinds, sums).atoms()) {
                if (!isLocalMember(module.name(), member)) {
                    bridgeCases.computeIfAbsent(member, k -> new ArrayList<>()).add(union);
                }
            }
        });
        Map<JvmClassName, TypeSymbol> byBridgeName = new LinkedHashMap<>();
        for (Map.Entry<TypeSymbol, List<GeneratedClass.BehaviorResult>> e : bridgeCases.entrySet()) {
            TypeSymbol member = e.getKey();
            JvmClassName cls = SoutherJvmAbi.nameOf(
                    new GeneratedClass.BridgeCase(module.name(), member));
            String bridge = cls.classDesc().displayName();
            Hir.BehaviorDef owner = behaviorNamed(module, e.getValue().get(0).behavior());
            SourcePos pos = owner.pos();
            TypeSymbol sameName = byBridgeName.put(cls, member);
            if (sameName != null) {
                // Each written as the identity it is: a module's with its module, and a primitive
                // as itself, which is what tells the two members apart.
                throw CompileException.of(Diagnostic.say(
                        new ModuleMessage.TwoMembersJoinThroughOneCaseClass(
                                String.valueOf(sameName), String.valueOf(member), bridge))
                        .at(pos)
                        .hint(new ModuleMessage.AMemberGoesByItsOwnNameWithCaseAfterIt()).build());
            }
            Hir.Def aData = localTypes.get(cls);
            String aBehavior = behaviorClassOwner.get(cls);
            if (aData != null || aBehavior != null) {
                String other = aData != null ? aData.name() : aBehavior;
                throw CompileException.of(Diagnostic.at(pos)
                        .say(aData != null
                                ? new ModuleMessage.AMemberReachesTheUnionThroughAData(
                                        owner.name(), member.name(), bridge, other)
                                : new ModuleMessage.AMemberReachesTheUnionThroughABehavior(
                                        owner.name(), member.name(), bridge, other))
                        .hint(new ModuleMessage.RenameTheMemberOrTheTypeItCollidesWith(bridge))
                        .build());
            }
        }
    }

    /**
     * Whether {@code member} is a type the module named {@code module} declared: the union's JVM
     * form and its Souther form are then the same values, and no bridge case is made for it. The
     * one place that is decided, for the check that refuses a collision of bridge cases and the
     * backend that writes them.
     */
    public static boolean isLocalMember(String module, TypeSymbol member) {
        return !member.isDeclaredByLanguage()
                && member instanceof TypeSymbol.AtModule at && at.module().equals(module);
    }

    /** The behavior of this module written under {@code name}. Every result union and every bridge
     *  case reaching here was built from one of these, so there is always one. */
    private static Hir.BehaviorDef behaviorNamed(Hir.Module module, String name) {
        for (Hir.BehaviorDef bd : module.behaviors()) {
            if (bd.name().equals(name)) {
                return bd;
            }
        }
        throw new IllegalStateException("no behavior named " + name + " in " + module.name());
    }
}
