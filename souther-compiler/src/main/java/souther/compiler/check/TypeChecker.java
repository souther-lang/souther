package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The slice-3 type checker. Adds a module symbol table so fields, decoders, and encoders
 * can reference other data types (e.g. {@code id: MemberId}, {@code field("id",
 * MemberId.decoder)}, {@code MemberId.encode(self.id)}). Exposes {@link #symbols} and
 * {@link #typeOf} for the backend; the type-level operations live in {@link TypeOps}.
 */
public final class TypeChecker {

    private TypeChecker() {}

    /**
     * What a successful check produced for the backend (issue #81): the Core of every body it typed,
     * carrying the type decided for each node, plus the warnings the check raised. The backend emits
     * from these rather than translating the AST and inferring the same types a second time.
     */
    public record Checked(Map<String, Core> behaviorBodies, Map<String, Core> recursiveHelpers,
                          List<Diagnostic> warnings) {}

    /** The bodies elaborated so far, filled as the check walks them. */
    static final class Elaborated {
        final Map<String, Core> behaviors = new LinkedHashMap<>();
        final Map<String, Core> helpers = new LinkedHashMap<>();
    }

    /**
     * A recovering check that keeps each error as the exception it was raised as, together with
     * what the check elaborated.
     *
     * <p>The only entry point. A caller decides what to do with what was found: raise the first, or
     * report them all. It hands back the exceptions rather than the diagnostics because a diagnostic
     * does not carry the English body a throw site passed alongside it, and a caller that has to
     * raise one should raise what the pass raised.
     */
    /**
     * @param errors what the check found wrong
     * @param abandoned the units it could not read at all, each resting on a name that denotes
     *                  nothing — reported already, and each a reason the module cannot be emitted
     */
    public record Reported(List<CompileException> errors, List<Unanswerable> abandoned,
                           Checked checked) {}

    public static Reported checkReporting(Ast.Module module, Symbols symbols,
                                          Map<String, Sig> importedSigs, Set<String> importedInjected,
                                          Ast.Module lowered) {
        List<Diagnostic> warnings = new ArrayList<>();
        Elaborated elaborated = new Elaborated();
        List<Unanswerable> abandoned = new ArrayList<>();
        List<CompileException> errors =
                checkCollecting(module, symbols, importedSigs, importedInjected, lowered, warnings,
                        elaborated, abandoned);
        return new Reported(errors, List.copyOf(abandoned),
                new Checked(elaborated.behaviors, elaborated.helpers, warnings));
    }

    /** Every error found in {@code module}, recovering past each so the whole module is checked; the
     * originating exceptions in the order they were found (so the first is the one the old fail-fast
     * check would have thrown), deduped. */
    static List<CompileException> checkCollecting(Ast.Module module, Symbols symbols,
                                                          Map<String, Sig> importedSigs,
                                                          Set<String> importedInjected, Ast.Module lowered,
                                                          List<Diagnostic> warnings, Elaborated elaborated) {
        return checkCollecting(module, symbols, importedSigs, importedInjected, lowered, warnings,
                elaborated, new ArrayList<>());
    }

    static List<CompileException> checkCollecting(Ast.Module module, Symbols symbols,
                                                          Map<String, Sig> importedSigs,
                                                          Set<String> importedInjected, Ast.Module lowered,
                                                          List<Diagnostic> warnings, Elaborated elaborated,
                                                          List<Unanswerable> abandoned) {
        List<CompileException> errors = new ArrayList<>();
        try {
            checkRecovering(module, symbols, importedSigs, importedInjected, lowered, errors, warnings,
                    elaborated, abandoned);
        } catch (Unanswerable e) {
            abandoned.add(e);
        } catch (CompileException e) {
            // A structural / prerequisite check (a duplicate name, an `exposing` violation, a module
            // cycle) is fail-fast: it can leave later phases without the state they read, so its first
            // error is recorded and the rest of the module is abandoned. Per-definition and
            // per-behavior errors are collected instead, so one broken body does not hide another.
            // An unresolvable type no longer gets here: it denotes the error type, which absorbs, so
            // the module is checked past it and never reaches codegen.
            errors.add(e);
        }
        return deduped(errors);
    }

    /** Runs one independent unit's check, recording its first error instead of throwing so the next
     * unit is still checked — the recovery boundary that lets a module report more than one error. */
    /**
     * Runs one unit's check, recording its first error instead of throwing so the next unit is still
     * checked — the recovery boundary that lets a module report more than one error.
     *
     * <p>A unit that was abandoned rather than found wrong is recorded in {@code abandoned}. It has
     * no error of its own: the name it rested on was reported where it was written. But the module
     * cannot be emitted, because this unit has no meaning to emit, and that is what the list says.
     */
    static void collect(List<CompileException> errors, List<Unanswerable> abandoned,
                        Runnable unitCheck) {
        try {
            unitCheck.run();
        } catch (CompileException e) {
            errors.add(e);
        } catch (Unanswerable e) {
            abandoned.add(e);
        }
    }

    /** Collected errors as a stable set in first-seen order: one per (code, message, region), so the
     * same underlying error reported by two phases is shown once. */
    static List<CompileException> deduped(List<CompileException> errors) {
        Map<String, CompileException> unique = new LinkedHashMap<>();
        for (CompileException e : errors) {
            unique.putIfAbsent(dedupKey(e.diagnostic()), e);
        }
        return new ArrayList<>(unique.values());
    }

    static String dedupKey(Diagnostic d) {
        if (d == null) {
            return "null";
        }
        Region r = d.region();
        String at = r == null ? "" : r.start() + ":" + r.end();
        return d.code() + "|" + d.messageKey() + "|" + d.literalMessage() + "|" + at;
    }


    /**
     * The check phases, appending to {@code errors} rather than returning them. Contract: each
     * independent per-definition or per-behavior check MUST be run through {@link #collect} so its
     * failure is recorded and the next unit is still checked. Only a phase that builds state a later
     * phase reads (the {@code fns} map, the {@code exposed} set, {@code reqSigs}, {@code sigs}) may
     * throw straight out — its caller treats that as fail-fast and abandons the module.
     */
    static void checkRecovering(Ast.Module module, Symbols symbols,
                                        Map<String, Sig> importedSigs, Set<String> importedInjected,
                                        Ast.Module lowered,
                                        List<CompileException> errors, List<Diagnostic> warnings,
                                        Elaborated elaborated, List<Unanswerable> abandoned) {
        Map<String, Ast.Expr> loweredBodies = new HashMap<>();
        for (Ast.FnDef fn : lowered.fns()) {
            loweredBodies.put(fn.name(), fn.body());
        }
        HelperInliner inliner = HelperInliner.forModule(module);
        Map<String, Type> recursiveHelperFns = HelperTyping.recursiveHelperSigs(inliner, symbols);
        // An invariant runs on every construction and must terminate (spec §invariant-expressions).
        // A total recursive helper does terminate, so it is admissible — including the stdlib fold
        // (`List.foldFrom`) that backs the list quantifiers `List.all`/`any`/`member`/`distinct`,
        // which are inlined down to it here (`withInlinedInvariants` runs before this check). Only a
        // `partial` helper — one that disclaims totality and may loop — is barred. A non-partial
        // recursive helper that is in fact non-total is caught later by the totality check.
        Set<String> partialRecursiveFns = new LinkedHashSet<>();
        for (String name : recursiveHelperFns.keySet()) {
            Ast.FnDef helper = inliner.helper(name);
            if (helper != null && helper.partial()) {
                partialRecursiveFns.add(name);
            }
        }
        // The invariant checks run before the data check, so a partial call or a construction is named
        // before it is otherwise reported as an unknown function or type-checked.
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data data && data.invariant().isPresent()) {
                Ast.Expr inv = data.invariant().get();
                HelperTyping.rejectPartialHelperInInvariant(inv, data.name(), partialRecursiveFns);
                HelperTyping.rejectConstructionInInvariant(inv, data.name());
            }
        }
        for (Ast.Def def : module.defs()) {
            collect(errors, abandoned, () -> {
                switch (def) {
                    case Ast.Data data ->
                            DataChecker.checkData(CheckContext.of(symbols).forData(data), recursiveHelperFns);
                    case Ast.SumData sum -> DataChecker.checkSum(sum, symbols);
                    case Ast.UnitData _ -> { }
                }
            });
        }
        collect(errors, abandoned, () -> DataChecker.checkNoUninhabitableCycle(module, symbols));
        Map<String, Ast.FnDef> fns = new HashMap<>();
        for (Ast.FnDef fn : module.fns()) {
            if (fns.put(fn.name(), fn) != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.dup.let").title("check.duplicate.title")
                                .at(fn.pos()).args(fn.name()).build(),
                        "duplicate `let " + fn.name() + "`");
            }
        }
        Set<String> allBehaviors = new HashSet<>();
        Set<String> specNames = new HashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            allBehaviors.add(b.name());
            if (b instanceof Ast.SpecBehavior spec) {
                specNames.add(b.name());
                SpecChecker.rejectAnonymousUnionParams(spec);
                SpecChecker.rejectTupleIO(spec);
                SpecChecker.rejectNonBoundaryMapKeyIO(spec, symbols);
                List<String> outputCases = new ArrayList<>();
                for (Ast.TypeRef t : spec.ret().cases()) {
                    outputCases.add(t.name());
                }
                DataChecker.rejectDuplicateNames(outputCases, "the behavior output", spec.pos());
                List<String> required = new ArrayList<>();
                for (Ast.ValueRef req : spec.requires()) {
                    required.add(req.bare());
                }
                DataChecker.rejectDuplicateNames(required, "`requires`", spec.pos());
                DataChecker.rejectDuplicateTypes(spec.constructs(), "`constructs`", spec.pos());
            }
        }
        // A data is Java-buildable from outside iff the whole module is public (no `exposing`) or
        // its name is exposed. Used by the injection constructs check (E1305).
        boolean exposeAll = module.exposing().isEmpty();
        // `exposing` lists a module's own public surface. A module's own type names, as opposed to
        // `symbols`, which also holds the data it imports — an imported name is not re-exported.
        Set<String> ownTypes = new HashSet<>();
        for (Ast.Def d : module.defs()) {
            ownTypes.add(d.name());
        }
        Set<String> exposed = new HashSet<>();
        for (String e : module.exposing()) {
            int dot = e.indexOf('.');
            // `exposing` is type-granular: a data's decoder/encoder are always public API once the
            // data itself is exposed (spec 19.4), so there is nothing a `.decoder`/`.encoder` member
            // could narrow. Reject it rather than accept a form that reads as a granularity that
            // does not exist.
            if (dot >= 0) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.exposing.granular").title("check.module.title")
                                .at(module.pos()).args(e.substring(0, dot), e).build(),
                        "`exposing` is type-granular: a data's `decoder`/`encoder` are always public"
                                + " once the data is exposed (spec 19.4). Write `" + e.substring(0, dot)
                                + "`, not `" + e + "`");
            }
            // an exposed name must be one of this module's own definitions. An imported name that is
            // merely visible here is not re-exported — importers reach it from its declaring module.
            if (!ownTypes.contains(e) && !allBehaviors.contains(e)) {
                boolean imported = symbols.inScope(e);
                String why = imported
                        ? " is imported into this module, not defined here; `exposing` lists a"
                          + " module's own definitions and does not re-export imported names"
                        : ", which is not a data or behavior of this module";
                throw CompileException.of(
                        Diagnostic.of(null, imported ? "check.exposing.imported" : "check.exposing.notdefined")
                                .title("check.module.title").at(module.pos()).args(e).build(),
                        "`exposing` names `" + e + "`" + why);
            }
            exposed.add(e);
        }
        // Injection targets (spec 13.2): a SpecBehavior with no matching fn. Its name and success
        // type let a fn call it inline (spec 12.2); it is the "required" behavior of the old form.
        // An imported injection target is one here too (spec 14.3): the module that names it injects
        // and binds it, whether it named it as a `>->` stage or as a `requires` dependency. Its
        // signature comes from the module that declared it; a local behavior of the same name wins.
        // The same map is built before the module is lowered, where a helper's parameter type is
        // settled from a call to an injected behavior (issue #178), so it is built in one place.
        Map<String, ReqSig> reqSigs = InjectionSigs.of(module, symbols, importedSigs, importedInjected);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec && !fns.containsKey(spec.name())) {
                // `requires` names what an implementation calls (12.6), and an injection target has
                // no implementation here — the Java side provides it (13.2). Declaring `requires` on
                // one is meaningless: nothing calls those behaviors, and nothing injects them. The
                // behavior that composes or calls this one carries the requirement instead (13.2).
                if (!spec.requires().isEmpty()) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.inject.requires").title("check.module.title")
                                    .at(spec.pos()).args(spec.name()).build(),
                            "behavior `" + spec.name() + "` has no `let`, so it is an injection target"
                                    + " (spec 13.2); it cannot declare `requires` — the behavior that"
                                    + " calls or composes it does");
                }
                SpecChecker.checkInjectionConstructs(spec, symbols, exposeAll, exposed);
            }
        }
        // Fail-fast with the reqSigs it reads: a `requires` that named something else leaves the call
        // untypeable, and the body check would report it as a call to an unknown name (E1401).
        SpecChecker.checkRequiresAreInjectionTargets(module, reqSigs);
        // A binding whose value is a lambda takes no annotation (spec 16.1). Read on the surface bodies:
        // lowering has already expanded such a binding away at each of its applications.
        for (Ast.FnDef fn : module.fns()) {
            collect(errors, abandoned, () -> Elaborator.rejectAnnotatedLambdaBindings(fn.body()));
        }
        // Helper fns (no matching behavior) are expanded inline at each call site (spec 12.5); a
        // helper is checked standalone against its own parameter types, which its body settles
        // (spec 13.1). Recovered so a broken helper does not hide the behavior-body errors below.
        collect(errors, abandoned, () -> HelperTyping.checkHelpers(inliner, symbols, reqSigs, recursiveHelperFns,
                loweredBodies, elaborated));
        // Recursion is total by default (spec §fn-declaration): a non-`partial` recursive helper must
        // be structurally recursive, so its examples terminate at compile time.
        collect(errors, abandoned, () -> TotalityChecker.check(inliner));
        // What each recursive helper constructs, transitively — a recursive helper is not inlined, so
        // its constructions are attributed to the behavior that calls it (spec 12.5).
        Map<String, Map<TypeName, String>> recHelperConstructs =
                HelperTyping.recursiveHelperConstructs(recursiveHelperFns.keySet(), loweredBodies, inliner, symbols);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                Ast.FnDef fn = fns.get(spec.name());
                if (fn != null) {
                    collect(errors, abandoned, () -> elaborated.behaviors.put(fn.name(),
                            SpecChecker.checkSpecFn(spec, fn, loweredBodies.get(spec.name()), symbols,
                            allBehaviors, reqSigs, inliner, recursiveHelperFns, recHelperConstructs,
                            warnings)));
                }
            }
        }
        // A fn matching a pipeline is rejected (a pipeline is already its own implementation, so it
        // cannot also have a fn body — spec 13.1). A fn matching a SpecBehavior is that behavior's
        // implementation (checked above); any other fn is a helper (checked by checkHelpers). These
        // terminal validations build no state, so each is recovered independently.
        collect(errors, abandoned, () -> {
            for (Ast.FnDef fn : module.fns()) {
                if (!specNames.contains(fn.name()) && allBehaviors.contains(fn.name())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.impl.compose").title("check.impl.title")
                                    .at(fn.pos()).args(fn.name()).build(),
                            "`let " + fn.name() + "` cannot implement the composition `behavior " + fn.name()
                                    + "`, which is already its own implementation (spec 13.1)");
                }
            }
        });
        collect(errors, abandoned, () -> SpecChecker.checkStagesAreSingleInput(module));
        // an exposed composition must declare its output in `exposing`, matching the inferred one
        // (spec 14.5, ADR-0024), so a far-away change cannot grow a published output silently.
        // `signatures` builds the map `checkExposedPipeOutputs` reads, so it stays fail-fast.
        collect(errors, abandoned, () -> SpecChecker.checkExposedPipeOutputs(module,
                exposed, PipelineSigs.signatures(module, symbols, importedSigs), symbols));
    }

    /** Applies {@code f} to every direct subexpression of {@code e}. Delegates to the one
     * exhaustive walk on the AST: written out here again, a node kind added later would fall
     * into a default and be skipped silently by every pass that recurses through this. */
    static void forEachChild(Ast.Expr e, java.util.function.Consumer<Ast.Expr> f) {
        Ast.forEachChild(e, f);
    }

    /** The symbol table of a module compiled on its own: bare names are its own definitions. */
    public static Symbols symbols(Ast.Module module) {
        return Symbols.of(module);
    }

    /** A module's own definitions, keyed by the name written there. */
    public static Map<String, Ast.Def> ownDefs(Ast.Module module) {
        Declared declared = declared(module);
        if (!declared.rejected().isEmpty()) {
            throw declared.rejected().get(0);
        }
        return declared.defs();
    }

    /** What a module declares, and the declarations it cannot have. */
    public record Declared(Map<String, Ast.Def> defs, List<CompileException> rejected) {}

    /**
     * Every declaration a module may have, by name, and one error per declaration it may not.
     *
     * <p>A name declared twice keeps the first: the second is reported and left out, so the rest of
     * the module still means what it means. Writing a declaration twice is what copying one looks
     * like halfway through, and taking every name in the file away until it is finished is the
     * opposite of useful.
     */
    public static Declared declared(Ast.Module module) {
        Map<String, Ast.Def> symbols = new LinkedHashMap<>();
        List<CompileException> rejected = new ArrayList<>();
        for (Ast.Def def : module.defs()) {
            if (def.name().equals("Some") || def.name().equals("None")) {
                // Some/None are the built-in Option cases (ADR-0011); a user data of the same name
                // would make a `| Some v` pattern ambiguous between Option and the user case, so the
                // declaration is rejected here rather than allowed to collide (ADR-0035).
                rejected.add(CompileException.of(
                        Diagnostic.of(null, "check.sum.optioncase").title("check.sum.title")
                                .at(def.pos(), def.name().length()).args(def.name()).build(),
                        "`" + def.name() + "` is a built-in Option case and cannot be declared as a data type"));
                continue;
            }
            if (symbols.containsKey(def.name())) {
                rejected.add(CompileException.of(
                        Diagnostic.of(null, "check.dup.data").title("check.duplicate.title")
                                .at(def.pos()).args(def.name()).build(),
                        "duplicate data `" + def.name() + "`"));
                continue;
            }
            symbols.put(def.name(), def);
        }
        return new Declared(symbols, List.copyOf(rejected));
    }

}
