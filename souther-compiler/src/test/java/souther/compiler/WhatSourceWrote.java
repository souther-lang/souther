package souther.compiler;

import java.lang.classfile.AttributedElement;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.ClassSignature;
import java.lang.classfile.CodeModel;
import java.lang.classfile.FieldModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.MethodSignature;
import java.lang.classfile.Signature;
import java.lang.classfile.attribute.EnclosingMethodAttribute;
import java.lang.classfile.attribute.InnerClassInfo;
import java.lang.classfile.attribute.MethodParameterInfo;
import java.lang.classfile.attribute.SignatureAttribute;
import java.lang.classfile.constantpool.Utf8Entry;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What the source wrote, read back off what javac made of it.
 *
 * <p>A class file is not a source model, and a structural rule that asks one question of it gets an
 * answer to another. Two questions come up wherever a rule is about values travelling together —
 * <em>which places did somebody write</em> and <em>which types does each of them name</em> — and
 * neither of the two texts a class file carries answers both:
 *
 * <ul>
 *   <li>the descriptor names every value that is handed over, the ones lowering added included, and
 *       has had its type arguments erased;
 *   <li>{@code MethodParameters} marks the ones the language added rather than somebody writing
 *       them, which is the one attribute whose subject that is — though what it marks without the
 *       build asking for parameter names is what the language mandated and not what a local class
 *       closed over;
 *   <li>the signature names what was written, and replaces a type variable with its own name, so
 *       the bound it was declared under is not among its arguments.
 * </ul>
 *
 * <p>Read one of them and the question the other answers goes unanswered: pick the descriptor and a
 * value closed over by a local class reads as a parameter somebody chose; pick the signature and a
 * term passed under a variable bounded by one is a term named nowhere. So both are read here, once,
 * and what comes out is the least a rule needs: the places, what each names, and whether source
 * wrote it.
 *
 * <p><b>What this does not decide.</b> Which pairs of types may meet, and what makes a meeting
 * allowed, belong to the rule asking — nothing here knows the name of a single type this compiler
 * declares. What is shared is the reading, so a rule added later does not interpret a class file
 * for itself and inherit whichever of the two holes its choice of text leaves.
 */
public final class WhatSourceWrote {

    private static final String METAFACTORY = "java.lang.invoke.LambdaMetafactory";

    /**
     * One place a value stands, and what is known about it.
     *
     * @param names the types it names, through wrapping and through the bounds of any variable it
     *              is written under
     * @param sourceLevel whether somebody wrote it, as against lowering adding it to carry what a
     *                    body closed over
     */
    public record Slot(Set<String> names, boolean sourceLevel) {

        public Slot {
            names = Set.copyOf(names);
        }
    }

    /**
     * Somewhere values stand together, and the code that answers for them.
     *
     * @param where what to call it in a report
     * @param slots the places, which may name one type from two texts and so appear more than once
     * @param bodies what was compiled for it — a method's own code and the code of every lambda
     *               written inside it, since a lambda's body is part of the method as written
     */
    public record Carrier(String where, List<Slot> slots, List<CodeModel> bodies) {

        public Carrier {
            slots = List.copyOf(slots);
            bodies = List.copyOf(bodies);
        }

        /** Whether any place here names one of {@code types}. */
        public boolean names(List<String> types) {
            return slots.stream().anyMatch(slot -> namesOne(slot, types));
        }

        /** Whether a place somebody wrote names one of {@code types}. */
        public boolean sourceNames(List<String> types) {
            return slots.stream().filter(Slot::sourceLevel).anyMatch(slot -> namesOne(slot, types));
        }

        /**
         * Whether the two meet here at all, in one place or in two.
         *
         * <p>Both named, and at least one of the places written. Two values a body closed over are
         * two locals of one scope, which nobody chose against the other: what lowering made of
         * them is a carrier because a closure needs one, not because the source put them together.
         * Once either side is written — a parameter, a component, a field — a caller picks that one
         * against whatever the other is, and the meeting is a choice however the rest arrived.
         */
        public boolean meet(List<String> left, List<String> right) {
            return meeting(left, right, false);
        }

        /**
         * Whether the two meet here in two places rather than in one.
         *
         * <p>For a rule about a caller lining one value up against another. One place naming both —
         * a map of the one to the other, a list of pairs — is a single thing to be handed, and
         * whether what is inside it agrees is a question about that thing rather than about this
         * carrier. A rule whose two types can be held to each other wants this one; a rule about
         * types that cannot be held to each other at all wants {@link #meet}, since for those there
         * is nothing the inside of such a container could be asked.
         */
        public boolean meetApart(List<String> left, List<String> right) {
            return meeting(left, right, true);
        }

        private boolean meeting(List<String> left, List<String> right, boolean apart) {
            for (int one = 0; one < slots.size(); one++) {
                for (int other = 0; other < slots.size(); other++) {
                    if (apart && one == other) {
                        continue;
                    }
                    Slot names = slots.get(one);
                    Slot beside = slots.get(other);
                    if (namesOne(names, left) && namesOne(beside, right)
                            && (names.sourceLevel() || beside.sourceLevel())) {
                        return true;
                    }
                }
            }
            return false;
        }

        private static boolean namesOne(Slot slot, List<String> types) {
            return types.stream().anyMatch(slot.names()::contains);
        }
    }

    /**
     * Where {@code model} keeps values: its fields, which are its components if it is a record.
     *
     * <p>One value of the class and one value of each instance are two places rather than one. What
     * a rule about values standing together is about is a value that has both at once, and a
     * constant of the class stands beside every instance there will ever be — so reading them as
     * one carrier would report a class for a pair no object of it holds.
     */
    public static List<Carrier> held(ClassModel model) {
        Map<String, Set<String>> bounds = boundsOf(model);
        List<Slot> ofTheClass = new ArrayList<>();
        List<Slot> ofAnInstance = new ArrayList<>();
        for (FieldModel field : model.fields()) {
            // A field lowering made is a local a body closed over, held where the body can reach
            // it. What a record declares is not one of those.
            Set<String> names = new LinkedHashSet<>(
                    named(field.fieldTypeSymbol().descriptorString(), bounds));
            signatureOf(field).ifPresent(each -> names.addAll(named(each, bounds)));
            Slot slot = new Slot(names, !field.flags().has(AccessFlag.SYNTHETIC));
            (field.flags().has(AccessFlag.STATIC) ? ofTheClass : ofAnInstance).add(slot);
        }
        List<Carrier> carriers = new ArrayList<>();
        if (!ofAnInstance.isEmpty()) {
            carriers.add(new Carrier(named(model), ofAnInstance, List.of()));
        }
        if (!ofTheClass.isEmpty()) {
            carriers.add(new Carrier(named(model) + " (what the class holds)", ofTheClass,
                    List.of()));
        }
        return List.copyOf(carriers);
    }

    /**
     * Where {@code model} hands values over: every method somebody wrote, and every lambda written
     * inside one.
     *
     * <p>A lambda is read at the site that makes it rather than at the method it was compiled to.
     * What it closed over is the call site's own arguments and what it is handed when it runs is
     * the type it was instantiated at, so the two are told apart by what the machine wrote down —
     * where the compiled method alone has them in one list, in an order that depends on whether
     * anything was bound to a receiver.
     *
     * <p><b>What a lambda is handed is named without what it was given.</b> The type a lambda was
     * instantiated at is a descriptor, so a parameter of it declared as a list of something is a
     * list here and the something is named nowhere. Nothing in the class file says otherwise: what
     * the metafactory is told is the erasure. So a value a lambda is handed is read for the type it
     * is and not for what that type was given, which is narrower than everywhere else here.
     */
    public static List<Carrier> handedOver(ClassModel model) {
        List<Carrier> carriers = new ArrayList<>();
        Map<String, Set<String>> classBounds = boundsOf(model);
        Map<String, MethodModel> lowered = new LinkedHashMap<>();
        for (MethodModel method : model.methods()) {
            if (method.flags().has(AccessFlag.SYNTHETIC)) {
                lowered.put(method.methodName().stringValue(), method);
            }
        }
        for (MethodModel method : model.methods()) {
            // What lowering made of a lambda is read at the site that made it, and a bridge says
            // again what the method it stands for already said.
            if (method.flags().has(AccessFlag.SYNTHETIC)) {
                continue;
            }
            List<CodeModel> bodies = new ArrayList<>();
            method.code().ifPresent(bodies::add);
            for (InvokeDynamicInstruction made : lambdasIn(method)) {
                // What the metafactory binds is a lambda only where the body it names is one the
                // compiler wrote. Naming a method or a constructor that was written is a reference
                // to it, and what that one is handed is read where it is declared — reading it
                // here as well would report the place that named it for a shape somebody else
                // wrote, and for a proof written where the reference cannot see it.
                MethodModel body = lowered.get(implementationOf(made));
                if (body == null) {
                    continue;
                }
                // A lambda's body is written inside the method, so what it does is what the method
                // does: a rule satisfied there is satisfied by the method that wrote it.
                List<CodeModel> its = new ArrayList<>();
                body.code().ifPresent(its::add);
                bodies.addAll(its);
                carriers.add(lambdaAt(model, method, made, classBounds, its));
            }
            carriers.add(new Carrier(named(model) + "#" + method.methodName().stringValue(),
                    slotsOf(method, classBounds), bodies));
        }
        return List.copyOf(carriers);
    }

    /** The lambda made at one site: what it closed over, and what it is handed when it runs. */
    private static Carrier lambdaAt(ClassModel model, MethodModel wrote,
            InvokeDynamicInstruction made, Map<String, Set<String>> bounds, List<CodeModel> its) {
        List<Slot> slots = new ArrayList<>();
        for (ClassDesc closed : made.typeSymbol().parameterList()) {
            slots.add(new Slot(named(closed.descriptorString(), bounds), false));
        }
        if (made.bootstrapArgs().size() > 2
                && made.bootstrapArgs().get(2) instanceof MethodTypeDesc when) {
            for (ClassDesc handed : when.parameterList()) {
                slots.add(new Slot(named(handed.descriptorString(), bounds), true));
            }
        }
        return new Carrier(named(model) + "#" + wrote.methodName().stringValue()
                + " (a lambda written in it)", slots, its);
    }

    /** The lambdas written in one method, which are the call sites bound by the metafactory. */
    private static List<InvokeDynamicInstruction> lambdasIn(MethodModel method) {
        List<InvokeDynamicInstruction> made = new ArrayList<>();
        CodeModel code = method.code().orElse(null);
        if (code == null) {
            return made;
        }
        for (var element : code) {
            if (element instanceof InvokeDynamicInstruction site
                    && METAFACTORY.equals(nameOf(site.bootstrapMethod().owner()))) {
                made.add(site);
            }
        }
        return made;
    }

    /** Which method the site's lambda was compiled to, where it was compiled to one at all. */
    private static String implementationOf(InvokeDynamicInstruction made) {
        List<ConstantDesc> arguments = made.bootstrapArgs();
        if (arguments.size() > 1 && arguments.get(1) instanceof DirectMethodHandleDesc handle) {
            return handle.methodName();
        }
        return "";
    }

    private static String nameOf(ClassDesc owner) {
        return owner.packageName() + "." + owner.displayName();
    }

    /**
     * The places a method hands values over.
     *
     * <p>Both texts, and what each of them is worth. Where javac wrote a signature, the signature
     * is what somebody wrote and the descriptor is only what is handed over — which is how a local
     * class, whose constructor is given every value its body closed over and a signature naming the
     * parameters that were written, says which of them is which.
     */
    private static List<Slot> slotsOf(MethodModel method, Map<String, Set<String>> classBounds) {
        List<ClassDesc> handed = method.methodTypeSymbol().parameterList();
        List<Boolean> added = addedByTheLanguage(method, handed.size());
        MethodSignature signature = signatureOf(method).map(MethodSignature::parseFrom).orElse(null);
        if (signature == null) {
            List<Slot> slots = new ArrayList<>();
            for (int at = 0; at < handed.size(); at++) {
                slots.add(new Slot(named(handed.get(at).descriptorString(), classBounds),
                        !added.get(at)));
            }
            return slots;
        }
        Map<String, Set<String>> bounds = boundsOf(signature.typeParameters(), classBounds);
        List<Signature> written = signature.arguments();
        if (written.size() != handed.size()) {
            // Two lists of different lengths are two lists: what javac wrote a signature of is what
            // the source declared, and which of the values handed over those are is not said
            // anywhere here. So each list is read for what it does say, and nothing is lined up.
            List<Slot> slots = new ArrayList<>();
            for (ClassDesc each : handed) {
                slots.add(new Slot(named(each.descriptorString(), bounds), false));
            }
            for (Signature each : written) {
                slots.add(new Slot(named(each.signatureString(), bounds), true));
            }
            return slots;
        }
        List<Slot> slots = new ArrayList<>();
        for (int at = 0; at < handed.size(); at++) {
            Set<String> names = new LinkedHashSet<>(named(handed.get(at).descriptorString(), bounds));
            names.addAll(named(written.get(at).signatureString(), bounds));
            slots.add(new Slot(names, !added.get(at)));
        }
        return slots;
    }

    /**
     * Which of the values handed over the language added rather than somebody writing them.
     *
     * <p>Said by {@code MethodParameters}, which is the attribute whose subject this is: an inner
     * class's constructor is handed the instance it is inside and says so there, and nothing else
     * in the class file does. What that attribute does not carry unless the build asks for names is
     * a local class's captures, which is why a signature is read beside it — a signature javac
     * wrote lists what the source declared, and whatever else is handed over is not that.
     */
    private static List<Boolean> addedByTheLanguage(MethodModel method, int handed) {
        List<Boolean> added = new ArrayList<>(Collections.nCopies(handed, false));
        method.findAttribute(Attributes.methodParameters()).ifPresent(said -> {
            List<MethodParameterInfo> parameters = said.parameters();
            for (int at = 0; at < parameters.size() && at < handed; at++) {
                added.set(at, parameters.get(at).has(AccessFlag.MANDATED)
                        || parameters.get(at).has(AccessFlag.SYNTHETIC));
            }
        });
        return added;
    }

    /**
     * What a piece of signature or descriptor text names.
     *
     * <p>Through what a type was given, since a pairing written as one map is one place naming two
     * types, and through what a variable was bounded by, since a value passed as an {@code N} where
     * {@code N} is some type is a value of that type by every name but the one it is written under.
     */
    private static Set<String> named(String text, Map<String, Set<String>> bounds) {
        Set<String> found = new LinkedHashSet<>();
        read(text, bounds, found, new LinkedHashSet<>());
        return found;
    }

    private static void read(String text, Map<String, Set<String>> bounds, Set<String> into,
            Set<String> seen) {
        int at = 0;
        while (at < text.length()) {
            char each = text.charAt(at);
            if (each != 'L' && each != 'T') {
                at++;
                continue;
            }
            int ends = at + 1;
            while (ends < text.length() && text.charAt(ends) != ';' && text.charAt(ends) != '<') {
                ends++;
            }
            if (ends >= text.length()) {
                return;
            }
            String said = text.substring(at + 1, ends);
            if (each == 'L') {
                into.add(said.replace('/', '.'));
            } else if (seen.add(said)) {
                // A variable stands for whatever it was bounded by, and a bound may be another
                // variable, so the walk is over the declaration and not one step of it.
                for (String bound : bounds.getOrDefault(said, Set.of())) {
                    read(bound, bounds, into, seen);
                }
            }
            at = ends;
        }
    }

    /**
     * What the variables in scope at {@code model} are bounded by.
     *
     * <p>Its own, and what it is written inside. A class written inside another stands where that
     * one's variables are in scope and may hold a value under one, so a bound read off the class in
     * hand alone leaves the value named nowhere — which is the hole this whole reading is about,
     * one level out. What says where a class was written is what the compiler put there: the entry
     * for it among the inner classes, or, for one written inside a method, the method it names.
     */
    private static Map<String, Set<String>> boundsOf(ClassModel model) {
        Map<String, Set<String>> bounds = new LinkedHashMap<>();
        for (String around : writtenInside(model)) {
            compiledHere(around).ifPresent(outer -> bounds.putAll(boundsOf(outer)));
        }
        bounds.putAll(boundsOf(writtenInsideAMethod(model), bounds));
        return signatureOf(model)
                .map(each -> boundsOf(ClassSignature.parseFrom(each).typeParameters(), bounds))
                .orElse(Map.copyOf(bounds));
    }

    /** The class this one was written inside, where the compiler wrote that down. */
    private static List<String> writtenInside(ClassModel model) {
        String itself = model.thisClass().asInternalName();
        List<String> around = new ArrayList<>();
        model.findAttribute(Attributes.innerClasses()).ifPresent(said -> {
            for (InnerClassInfo each : said.classes()) {
                if (each.innerClass().asInternalName().equals(itself)) {
                    each.outerClass().ifPresent(outer ->
                            around.add(outer.asInternalName().replace('/', '.')));
                }
            }
        });
        model.findAttribute(Attributes.enclosingMethod()).ifPresent(said ->
                around.add(said.enclosingClass().asInternalName().replace('/', '.')));
        return around;
    }

    /**
     * The variables declared by the method a class was written inside.
     *
     * <p>Looked up rather than read off the entry: what {@code EnclosingMethod} carries is the
     * method's descriptor, where a variable has already been replaced by what it was bounded by, so
     * the declaration is the method's own and is where that method was compiled.
     */
    private static List<Signature.TypeParam> writtenInsideAMethod(ClassModel model) {
        EnclosingMethodAttribute said = model.findAttribute(Attributes.enclosingMethod())
                .orElse(null);
        if (said == null || said.enclosingMethodName().isEmpty()) {
            return List.of();
        }
        String named = said.enclosingClass().asInternalName().replace('/', '.');
        ClassModel around = compiledHere(named).orElse(null);
        if (around == null) {
            return List.of();
        }
        for (MethodModel each : around.methods()) {
            if (each.methodName().equalsString(said.enclosingMethodName().get().stringValue())
                    && each.methodType().equalsString(
                            said.enclosingMethodType().orElseThrow().stringValue())) {
                return signatureOf(each)
                        .map(MethodSignature::parseFrom)
                        .map(MethodSignature::typeParameters)
                        .orElse(List.of());
            }
        }
        return List.of();
    }

    /**
     * The same for a list of declarations, over whatever was in scope already.
     *
     * <p>A method's own variable stands for what the method declared it as, whatever a class of the
     * same spelling declared, which is what a name declared twice means everywhere else.
     */
    private static Map<String, Set<String>> boundsOf(List<Signature.TypeParam> declared,
            Map<String, Set<String>> outer) {
        if (declared.isEmpty()) {
            return outer;
        }
        Map<String, Set<String>> bounds = new LinkedHashMap<>(outer);
        for (Signature.TypeParam each : declared) {
            Set<String> written = new LinkedHashSet<>();
            each.classBound().map(Signature::signatureString).ifPresent(written::add);
            each.interfaceBounds().stream().map(Signature::signatureString).forEach(written::add);
            bounds.put(each.identifier(), written);
        }
        return Map.copyOf(bounds);
    }

    private static String named(ClassModel model) {
        return model.thisClass().asInternalName().replace('/', '.');
    }

    /**
     * A class this module compiled, wherever it put it.
     *
     * <p>Both of its outputs, because this reading is asked of both: what a rule is about is what
     * the module compiled, and what holds this reading to what it claims is written beside the
     * rules. A class written inside another is looked up here, so looking in one output would make
     * the answer depend on which of the two the class in hand came from.
     */
    private static Optional<ClassModel> compiledHere(String named) {
        return WhatWasCompiled.compiled().find(named)
                .or(() -> WhatWasCompiled.checksCompiledBesideIt().find(named));
    }

    private static Optional<String> signatureOf(AttributedElement element) {
        return element.findAttribute(Attributes.signature())
                .map(SignatureAttribute::signature)
                .map(Utf8Entry::stringValue);
    }

    private WhatSourceWrote() {
    }
}
