package souther.architecture;

import souther.test.Signatures;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.ClassSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.RecordAttribute;
import java.lang.classfile.attribute.RecordComponentInfo;
import java.lang.classfile.attribute.SignatureAttribute;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What the types a signature is written in reach.
 *
 * <p>The closure read from the roots it is given: the types the signature names, the declared upper
 * bounds of the type variables it refers to, and the components of the records it arrives at. A rule
 * about a surface is written against this so that it holds of what a caller can be handed rather
 * than of how the handing was spelled — a clause inside a record is a clause the caller gets, and a
 * world named through a variable is the world the declaration guarantees.
 *
 * <p><b>A bound is read because it is what the declaration guarantees, not because it says what the
 * argument will be.</b> {@code <S extends Symbols>} may be given a derived world and this reading
 * does not say so; what it says is that {@code Symbols} is what every use of {@code S} is warranted
 * to be. That is the same answer to both of the questions a rule asks — whether a world could arrive
 * here at all, and whether the one that arrives is the derived one — so one reading serves both, and
 * a walk bounded only by {@code Symbols} stays loose under the rule that wants the derived world.
 *
 * <p><b>A type parameter is an environment and not a root.</b> A bound is followed when the variable
 * it belongs to is referred to from a root, and not before: a method declaring
 * {@code <S extends DerivedSymbols>} and never writing {@code S} reaches nothing through it.
 *
 * <p><b>What this cannot resolve, it does not call unreachable.</b> A type variable with no binding
 * in scope and a class of this repository with no class file are both questions this reading cannot
 * answer, and both fail it. Answering {@code false} there is the shape of the defect this reading
 * replaced: a spelling nobody had thought of went unread and was reported as reaching nothing.
 *
 * <p>What it does not do is recover what a signature threw away. A raw type, or a parameter written
 * as {@code Object}, names nothing this can follow, and no reading of the signature will say what
 * flows through it. Nor does it substitute the arguments at a use into the components of the record
 * they parameterize: an argument is written where the record is used and is already read there, and
 * a bound is the only thing a signature refers to without spelling it. A question about which
 * component becomes which type would need that substitution and is not one this answers.
 */
final class WhatASignatureReaches {

    private static final String OF_THIS_REPOSITORY = "souther/";

    private final CompiledClasses compiled;

    WhatASignatureReaches(CompiledClasses compiled) {
        this.compiled = compiled;
    }

    /** Whether any of {@code roots}, read in {@code scope}, reaches one of {@code wanted}. */
    boolean anyOf(List<Signature> roots, Scope scope, Set<String> wanted) {
        Walk walk = new Walk(wanted);
        for (Signature root : roots) {
            if (walk.reaches(root, scope)) {
                return true;
            }
        }
        return false;
    }

    /** Whether {@code root}, read in {@code scope}, reaches one of {@code wanted}. */
    boolean reaches(Signature root, Scope scope, Set<String> wanted) {
        return anyOf(List.of(root), scope, wanted);
    }

    /** The signature of one record component, generic or not, as this reading takes it. */
    static Signature componentSignature(RecordComponentInfo component) {
        return component.findAttribute(Attributes.signature())
                .map(SignatureAttribute::asTypeSignature)
                .orElseGet(() -> Signature.of(component.descriptorSymbol()));
    }

    /** What a type parameter declares its variable to be: the class bound where there is one, and
     *  the interface bounds, which is where a variable bounded only by interfaces says so. */
    static List<Signature.RefTypeSig> boundsOf(Signature.TypeParam declared) {
        List<Signature.RefTypeSig> out =
                new ArrayList<>(declared.classBound().map(List::of).orElse(List.of()));
        out.addAll(declared.interfaceBounds());
        return out;
    }

    /** The type parameters a class declares, none where it declares no signature of its own. */
    static List<Signature.TypeParam> typeParametersOf(ClassModel owner) {
        return owner.findAttribute(Attributes.signature())
                .map(SignatureAttribute::asClassSignature)
                .map(ClassSignature::typeParameters)
                .orElse(List.of());
    }

    /** One reading, holding what it has already been through. */
    private final class Walk {

        private final Set<String> wanted;

        /** The records already opened. Their components were read under their own scope, which is
         *  the same one however this arrived at them, so a second visit answers nothing new. */
        private final Set<String> opened = new LinkedHashSet<>();

        /** The bindings already followed, which is a different loop from the one above: a variable
         *  bounded by its own type is ordinary Java, and the closure of a bound is finite. */
        private final Set<Scope.Binding> followed = new LinkedHashSet<>();

        private Walk(Set<String> wanted) {
            this.wanted = wanted;
        }

        private boolean reaches(Signature type, Scope scope) {
            return switch (type) {
                case Signature.BaseTypeSig _ -> false;
                case Signature.ArrayTypeSig array -> reaches(array.componentSignature(), scope);
                case Signature.TypeVarSig variable -> reachesThroughBounds(variable, scope);
                case Signature.ClassTypeSig named -> reachesThroughClass(named, scope);
            };
        }

        private boolean reachesThroughArgument(Signature.TypeArg argument, Scope scope) {
            return switch (argument) {
                case Signature.TypeArg.Unbounded _ -> false;
                case Signature.TypeArg.Bounded bounded -> reaches(bounded.boundType(), scope);
            };
        }

        private boolean reachesThroughBounds(Signature.TypeVarSig variable, Scope scope) {
            Scope.Binding binding = scope.bindingOf(variable.identifier());
            if (!followed.add(binding)) {
                return false;
            }
            for (Signature.RefTypeSig bound : binding.bounds()) {
                if (reaches(bound, scope)) {
                    return true;
                }
            }
            return false;
        }

        private boolean reachesThroughClass(Signature.ClassTypeSig named, Scope scope) {
            String name = Signatures.named(named);
            if (wanted.contains(name)) {
                return true;
            }
            for (Signature.TypeArg argument : named.typeArgs()) {
                if (reachesThroughArgument(argument, scope)) {
                    return true;
                }
            }
            Optional<Signature.ClassTypeSig> outer = named.outerType();
            if (outer.isPresent() && reachesThroughClass(outer.get(), scope)) {
                return true;
            }
            return reachesThroughComponents(name);
        }

        private boolean reachesThroughComponents(String named) {
            // A class of another repository holds nothing of this one, so there is no record of
            // theirs to open. Which is a definition and not an absence: what a name of theirs
            // reaches was answered by the arguments written beside it.
            if (!named.startsWith(OF_THIS_REPOSITORY) || !opened.add(named)) {
                return false;
            }
            ClassModel owner = compiled.read(named);
            Optional<RecordAttribute> components = owner.findAttribute(Attributes.record());
            if (components.isEmpty()) {
                return false;
            }
            // Replaced and not layered: a record is static wherever it is written, so the variables
            // a component names are its own and never the ones in scope where it was reached.
            Scope inside = Scope.of(named, typeParametersOf(owner));
            for (RecordComponentInfo component : components.get().components()) {
                if (reaches(componentSignature(component), inside)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * What the type variables in scope stand for.
     *
     * <p>Built by whoever holds a signature, because which bindings are in scope is a fact about
     * where the signature was written and not one the signature carries: a method's own parameters
     * over the ones its class declares, and a name declared in both is the method's.
     */
    record Scope(Map<String, Binding> bindings) {

        static Scope of(String owner, List<Signature.TypeParam> declared) {
            return new Scope(Map.of()).and(owner, declared);
        }

        /** This scope with {@code declared} over it, where a repeated name is the newer binding. */
        Scope and(String owner, List<Signature.TypeParam> declared) {
            Map<String, Binding> out = new LinkedHashMap<>(bindings);
            for (Signature.TypeParam each : declared) {
                out.put(each.identifier(), new Binding(owner, each.identifier(), each));
            }
            return new Scope(out);
        }

        Binding bindingOf(String identifier) {
            Binding found = bindings.get(identifier);
            if (found == null) {
                throw new AssertionError("the type variable " + identifier + " is bound nowhere this"
                        + " reading was given, so what it stands for is a question this cannot"
                        + " answer; the scope holds " + bindings.keySet());
            }
            return found;
        }

        /** One type variable, told apart by what declared it: a method may name a variable its own
         *  class also names, and the two are two. */
        record Binding(String owner, String identifier, Signature.TypeParam declared) {

            List<Signature.RefTypeSig> bounds() {
                return boundsOf(declared);
            }
        }
    }
}
