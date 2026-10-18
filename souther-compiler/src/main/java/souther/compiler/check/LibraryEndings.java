package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.AbortSites;
import souther.compiler.ast.Hir;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * What each operation of a library may end a run without a value for, over every call of it and
 * everything the call runs: a kernel's own is {@link KernelContracts}', and one the library writes in
 * the language ends a run for what its body does. {@link Endings.Known} of none is said only where
 * nothing it runs ends one, whatever it is handed.
 *
 * <p>Read off the body from the same owners, and never classified a second time: what an operator in
 * it ends a run for is {@link AbortSites}', and what another operation it calls ends one for is this
 * table's own. A body's operands carry no type, so an operator is answered by the sites every typing
 * of it is written as ({@link AbortSites#ofAnOperatorOfAnyType}), which is no less than the sites of
 * one typing end a run for. {@link AbortSites} answers what each site ends a run for on its own; what
 * a site runs beyond itself is this reading's to follow, and an invariant a construction runs is not
 * in this tree.
 *
 * <p>A function runs where it is applied, and every place one is applied is not known here: a
 * function the body is handed or binds, applied by the body; a parameter the library applies in a
 * body of its own; and a kernel handed a function, whose contract answers for what the kernel itself
 * does and not for what the function it applies does. So a closure the body builds, and an operation
 * of the library it names without applying, run nothing of their own where they stand.
 *
 * <p>Also not known: a construction, whose invariant is its declaration's; an attempt at one, whose
 * refusal takes another arm; an operation coming back to itself, directly or through another, until
 * the cycle is read, and this reads none.
 *
 * <p>A pure function of a library, and the shipped one's is held once — the pattern
 * {@link LibraryReadThrough} follows.
 */
final class LibraryEndings {

    private static final Endings NONE = new Endings.Known(AbortSet.NONE);
    private static final Endings NOT_KNOWN = new Endings.NotKnown();

    private final Map<ValueName.Stdlib.Operation, Endings> ending;

    private LibraryEndings(Map<ValueName.Stdlib.Operation, Endings> ending) {
        this.ending = Map.copyOf(ending);
    }

    /** What every operation of {@code library}, and every sugar for one, ends a run for. */
    static LibraryEndings of(Stdlib library) {
        Reading reading = new Reading(library);
        library.entries().keySet().forEach(reading::of);
        library.rewrites().keySet().forEach(reading::of);
        return new LibraryEndings(reading.settled);
    }

    /** The shipped library's, which is the same for every compilation. */
    static LibraryEndings shipped() {
        return Shipped.ENDINGS;
    }

    private static final class Shipped {
        private static final LibraryEndings ENDINGS = of(DefaultStdlib.get());
    }

    /**
     * What {@code operation} ends a run for.
     *
     * @throws IllegalArgumentException where the library has no such operation — never answered as
     *     not known, which says the operation was read and its body did not say
     */
    Endings of(ValueName.Stdlib.Operation operation) {
        Endings found = ending.get(operation);
        if (found == null) {
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of the library read");
        }
        return found;
    }

    /** One reading of a library, each operation settled once. */
    private static final class Reading {
        private final Stdlib library;
        private final Map<ValueName.Stdlib.Operation, Endings> settled = new HashMap<>();
        private final Set<ValueName.Stdlib.Operation> reading = new HashSet<>();

        private Reading(Stdlib library) {
            this.library = library;
        }

        /**
         * What {@code operation} ends a run for. One met again while its own body is being read is
         * on a cycle, and so is everything read between the two meetings, which comes back to it.
         */
        Endings of(ValueName.Stdlib.Operation operation) {
            Endings done = settled.get(operation);
            if (done != null) {
                return done;
            }
            if (!reading.add(operation)) {
                return NOT_KNOWN;
            }
            Endings out = worked(operation);
            reading.remove(operation);
            settled.put(operation, out);
            return out;
        }

        private Endings worked(ValueName.Stdlib.Operation operation) {
            Stdlib.Intrinsic intrinsic = library.intrinsicOf(operation);
            if (intrinsic != null) {
                return handedAFunction(operation) ? NOT_KNOWN
                        : new Endings.Known(KernelContracts.abortsOf(intrinsic.kernel()));
            }
            Hir.FnDef declaration = library.helpers().get(operation);
            if (declaration != null) {
                return of(declaration.writtenBody());
            }
            Stdlib.Rewrite rewrite = library.rewriteOf(operation);
            if (rewrite != null) {
                return of(rewrite.target());
            }
            throw new IllegalArgumentException(
                    "`" + operation.qualified() + "` is no operation of this library");
        }

        /** Whether the kernel {@code operation} is takes a function, which it may apply. */
        private boolean handedAFunction(ValueName.Stdlib.Operation operation) {
            Stdlib.Entry entry = library.entry(operation);
            if (entry == null) {
                throw new IllegalStateException(
                        "`" + operation.qualified() + "` is a kernel the library declares no entry for");
            }
            return entry.signature().params().stream().anyMatch(Type.FnOf.class::isInstance);
        }

        /** What working {@code e} out, and everything under it it works out, ends a run for. */
        private Endings of(Hir.Expr e) {
            Endings[] out = {itself(e)};
            if (e instanceof Hir.Block) {
                return out[0];
            }
            Hir.forEachChild(e, child -> {
                if (out[0] instanceof Endings.Known) {
                    out[0] = out[0].and(of(child));
                }
            });
            return out[0];
        }

        /**
         * What {@code e} itself, and none of what it is made of, ends a run for.
         *
         * <p>Exhaustive over {@link Hir.Expr}, so a node kind added later stops the build here.
         */
        private Endings itself(Hir.Expr e) {
            return switch (e) {
                case Hir.Binary binary -> operator(binary);
                case Hir.Neg _ -> new Endings.Known(AbortSites.ofANegationOfAnyType());
                case Hir.Unreachable _ -> new Endings.Known(AbortSites.ofAnUnreachableWherever());
                case Hir.Apply apply -> applied(apply);
                case Hir.Var name -> read(name);
                case Hir.NewData _, Hir.IfConstructed _, Hir.Expansion _, Hir.Materialised _,
                     Hir.ValueBuild _, Hir.ValueInvocation _ -> NOT_KNOWN;
                case Hir.IntLit _, Hir.DecimalLit _, Hir.StringLit _, Hir.BoolLit _,
                     Hir.FieldAccess _, Hir.Match _, Hir.If _, Hir.ListLit _, Hir.RowCollection _,
                     Hir.ListComp _, Hir.LetIn _, Hir.Block _, Hir.Tuple _, Hir.TupleGet _ -> NONE;
            };
        }

        /**
         * What the sites an operator is written as end a run for ({@link AbortSites}), where that
         * is all they run. Where an unheld invariant is among the reasons, a construction may stand
         * there, and so may the invariant clauses it runs: those are its declaration's, not in this
         * tree, and what they end a run for is not known here.
         */
        private static Endings operator(Hir.Binary binary) {
            AbortSet sites = AbortSites.ofAnOperatorOfAnyType(binary.op());
            return sites.contains(AbortKind.INVARIANT_NOT_HELD)
                    ? NOT_KNOWN : new Endings.Known(sites);
        }

        /** An application of an operation of the library is what that operation ends a run for;
         *  of anything else, a function this body is handed or binds, it is not known. */
        private Endings applied(Hir.Apply apply) {
            return apply.function() instanceof Hir.Var.Denoting callee
                    && callee.reachedAs() instanceof ReachName.OfLibrary library
                    ? of(library.denotes()) : NOT_KNOWN;
        }

        /**
         * A name read: an operation of the library that takes nothing is worked out where it is
         * read, and anything else names a value already worked out or a function, which runs where
         * it is applied. A name that names nothing says nothing of what it reads.
         */
        private Endings read(Hir.Var name) {
            return switch (name) {
                case Hir.Var.Denoting denoting
                        when denoting.reachedAs() instanceof ReachName.OfLibrary library -> {
                    Stdlib.Entry entry = this.library.entry(library.denotes());
                    yield entry != null && entry.signature().params().isEmpty()
                            ? of(library.denotes()) : NONE;
                }
                case Hir.Var.Denoting _ -> NONE;
                case Hir.Var.Unanswered _ -> NOT_KNOWN;
            };
        }
    }
}
