package souther.compiler.check;

import souther.compiler.core.CompleteSignature;
import souther.compiler.core.DeclaredOperation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.ArgumentsStand;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.proof.ByPlace;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.MapPart;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.TakenAs;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;
import java.util.function.UnaryOperator;

/**
 * Holds what is declared of the language's operations to what the library declares, and answers
 * with the facts as bound.
 *
 * <p>A fact names an argument of an operation, and what an operation's arguments are is the
 * library's to say. Where the two disagree there is nothing to be done at a call — the fact is
 * about an argument that is not there, or is not the kind of thing the fact is about — so it is
 * said before any call is read rather than met as a missing answer at whichever reader arrives
 * first.
 *
 * <p><b>The one reader of the authoring vocabulary below the declarations, and the one place an
 * {@link ArgumentRef} becomes a position.</b> Everything below the binding holds a
 * {@link BoundOperationFact}, in which every operation is a {@link DeclaredOperation} and every
 * argument a {@link DeclaredArgument}; what those are made of — a word, a name, a signature, what
 * {@link Combinators} says an operation hands its closure — is read here and nowhere after.
 * {@code OnlyTheBinderReadsTheAuthoringVocabularyTest} counts that.
 *
 * <p><b>Over the declarations and not over what a reader asked for.</b> Bound one fact at a time as
 * it was looked up, a fact nothing looked up was a fact nothing checked, and how much of the
 * declaration was validated depended on which consumers a compilation happened to have. This walks
 * the whole list, so a fact declared is a fact held to the library whether or not anything reads
 * it.
 *
 * <p><b>Each declaration read once, before the switch.</b> The operation a fact is about is read
 * against the library into a {@link CompleteSignature} for every declaration, outside the switch,
 * and every arm is handed that reading. So being declared is what holds a fact to the library
 * rather than being a kind that happens to name an argument, and no arm reads the operation a
 * second time to ask where an argument is.
 *
 * <p><b>The switch is an expression.</b> Every arm yields the bound fact its kind comes to, so a
 * kind of fact added to the declarations is a kind that does not compile until this says what it
 * is once bound — an empty arm was how a kind went through held to nothing, and there is no empty
 * arm in an expression.
 *
 * <p>The second way into {@link CompleteSignature#ofDeclaration} beside {@link Preserved}, and on
 * the same warrant: a library declaration, read whole. {@code Preserved} is what a representation
 * keeps standing, which is a policy about representations and not about which operations the
 * library has, so a fact about an operation nothing keeps standing could not borrow its reading
 * from there.
 */
final class OperationFactBinder {

    /**
     * Holds every fact of {@code declared} to the library, and answers with what the walk came to.
     *
     * <p>The source is a parameter so that what this covers can be asked of it with a source of
     * one's own. Reading {@link OperationFacts#declarations()} directly, a test could show that the
     * facts there are valid and not that a fact added later would be visited at all.
     *
     * <p>Two passes and not one. Each fact is held to its own declaration as it is met; what one
     * fact may not say beside another — that a number is read by one representation — is asked of
     * all of them together once every one is bound, since a question about the set cannot be
     * answered from the order the declarations happen to come in.
     *
     * @param proofs how what is stated of the operations the library writes is proved of their
     *               bodies
     */
    static BoundOperationFacts bindAll(Stdlib stdlib, List<OperationFacts.Declared> declared,
                                       LibraryProofs.Source proofs) {
        List<OperationFacts.Declared> memberships = memberships(declared);
        List<BoundOperationFact> bound = new ArrayList<>();
        for (OperationFacts.Declared each : declared) {
            CompleteSignature declaration = declaredSignature(stdlib, each.operation());
            BoundOperationFact one = bind(stdlib, declaration, each.fact());
            LawProposition<ArgumentRef> beside = besideTheMembership(stdlib, each, memberships);
            bound.add(beside == null ? one : new BoundOperationFact.HasALaw(one.operation(),
                    ((BoundOperationFact.HasALaw) one).law(),
                    List.of(slots(stdlib, declaration, beside, false))));
        }
        // What the declarations may not say beside one another is asked of all of them, before
        // anything is proved: it is a question about the declarations, which no proof changes, and
        // a declaration refused is one nothing should be proved for.
        holdEachNumberToOneReading(stdlib,
                new BoundOperationFacts(stdlib, bound, LibraryProofs.TAKEN_AS_HOLDING));
        holdWhereElementsCameFromToOneAccount(bound);
        return new BoundOperationFacts(stdlib, bound, proofs);
    }

    /**
     * Refuses an operation that says where its elements came from twice, as a building and as a
     * lineage declared alone.
     *
     * <p>A building says it beside a count and a lineage says it without one, so an operation with
     * both has two answers to one question and a reader would take whichever it asked first. The
     * same kind said twice is refused where the facts are filed; two kinds saying one thing are
     * only seen beside each other.
     */
    private static void holdWhereElementsCameFromToOneAccount(List<BoundOperationFact> bound) {
        Set<ValueName> built = new HashSet<>();
        for (BoundOperationFact each : bound) {
            if (each instanceof BoundOperationFact.BuildsItsResultFrom) {
                built.add(each.operation().operation());
            }
        }
        for (BoundOperationFact each : bound) {
            if (each instanceof BoundOperationFact.ElementsComeFrom
                    && built.contains(each.operation().operation())) {
                throw new IllegalStateException(each.operation().operation()
                        + " says where its elements came from as a building and again alone;"
                        + " a building already says it");
            }
        }
    }

    /** The same, each written operation's facts proved here against its body. */
    static BoundOperationFacts bindAll(Stdlib stdlib, List<OperationFacts.Declared> declared) {
        return bindAll(stdlib, declared, LibraryProofs.PROVING);
    }

    /** The same, over what the language declares. */
    static BoundOperationFacts bindAll(Stdlib stdlib) {
        return bindAll(stdlib, LibraryProofs.PROVING);
    }

    /** The same, over what the language declares, with what is proved of the operations the
     *  library writes come by through {@code proofs}. */
    static BoundOperationFacts bindAll(Stdlib stdlib, LibraryProofs.Source proofs) {
        return bindAll(stdlib, OperationFacts.declarations(), proofs);
    }

    /** Every declaration of {@code declared} that is a truth law saying a container holds a
     *  value. */
    private static List<OperationFacts.Declared> memberships(
            List<OperationFacts.Declared> declared) {
        List<OperationFacts.Declared> out = new ArrayList<>();
        for (OperationFacts.Declared each : declared) {
            if (each.fact() instanceof OperationFact.HasALaw(
                    OperationLaw.Observation<ArgumentRef>(AnswerAspect aspect,
                            LawProposition<ArgumentRef> holds))
                    && aspect == AnswerAspect.TRUTH && aMembership(holds) != null) {
                out.add(each);
            }
        }
        return out;
    }

    /** {@code holds} where it says some element of a container, or a key of one, is a value
     *  handed beside it — or null where it says anything else. */
    private static LawProposition.SomeElement<ArgumentRef> aMembership(
            LawProposition<ArgumentRef> holds) {
        return holds instanceof LawProposition.SomeElement<ArgumentRef>(ArgumentRef container,
                LawProposition.Same<ArgumentRef>(LawSubject<ArgumentRef> named,
                        LawSubject.Argument<ArgumentRef> _, boolean alike), boolean some)
                && alike && namesAnElementOf(named, container) != null
                ? (LawProposition.SomeElement<ArgumentRef>) holds : null;
    }

    /** The membership {@code declared}, one of {@link #memberships}, states. */
    private static LawProposition.SomeElement<ArgumentRef> membershipOf(
            OperationFacts.Declared declared) {
        return aMembership(((OperationLaw.Observation<ArgumentRef>)
                ((OperationFact.HasALaw) declared.fact()).law()).equivalentTo());
    }

    /** The argument a membership says is held, or as a key. */
    private static ArgumentRef heldIn(LawProposition.SomeElement<ArgumentRef> membership) {
        return ((LawSubject.Argument<ArgumentRef>) ((LawProposition.Same<ArgumentRef>)
                membership.ofTheElement()).other()).argument();
    }

    /** How a membership names what a container holds: as an element, or as a key. */
    private enum Held { AS_AN_ELEMENT, AS_A_KEY }

    /** How {@code named} is what {@code container} holds — or null where it is neither an element
     *  of it nor a key of one. */
    private static Held namesAnElementOf(LawSubject<ArgumentRef> named, ArgumentRef container) {
        return switch (named) {
            case LawSubject.ElementOf<ArgumentRef>(ArgumentRef of) when of.equals(container) ->
                    Held.AS_AN_ELEMENT;
            case LawSubject.KeyOf<ArgumentRef>(ArgumentRef of) when of.equals(container) ->
                    Held.AS_A_KEY;
            default -> null;
        };
    }

    /**
     * How many a kernel's answer holds, where its law says it in cases a membership decides, said
     * beside what the operation that answers the membership answers — or null where {@code each}
     * is no such law.
     *
     * <p>Derived and not declared. A case written as some element being a value is what the
     * operation whose truth law says so answers, and a proof taking what is stated of that
     * operation beside others meets the cases only where they are said in its words. Declared a
     * second time, the two would be two statements of one fact that nothing holds to one another.
     */
    private static LawProposition<ArgumentRef> besideTheMembership(Stdlib stdlib,
            OperationFacts.Declared each, List<OperationFacts.Declared> memberships) {
        if (!(each.fact() instanceof OperationFact.HasALaw(OperationLaw.Size<ArgumentRef> size))
                || size.unconditional() != null
                || stdlib.intrinsicOf(theLibraryOperation(each.operation())) == null) {
            return null;
        }
        int arity = declaredSignature(stdlib, each.operation()).params().size();
        List<LawSubject<ArgumentRef>> own = new ArrayList<>();
        for (int at = 0; at < arity; at++) {
            own.add(new LawSubject.Argument<>(new ArgumentRef.At(at)));
        }
        LawNumber<ArgumentRef> itsSize = new LawNumber.SizeOf<>(new LawSubject.AnswerOf<>(
                theLibraryOperation(each.operation()), own));
        List<LawProposition<ArgumentRef>> cases = new ArrayList<>();
        boolean said = false;
        List<Type> takes = declaredSignature(stdlib, each.operation()).params();
        for (OperationLaw.Size.Case<ArgumentRef> one : size.cases()) {
            LawProposition<ArgumentRef> where = inItsWords(stdlib, takes, one.where(),
                    memberships);
            said |= !where.equals(one.where());
            Map<LawNumber<ArgumentRef>, ExactRatio> less = new LinkedHashMap<>();
            less.put(itsSize, ExactRatio.ONE);
            // A law is over the operation's arguments and never its own answer, so no number of
            // the case is the size it is equal to.
            one.equalTo().coefs().forEach((number, by) -> less.put(number, by.negated()));
            cases.add(new LawProposition.All<>(List.of(where, new LawProposition.Compared<>(
                    new LinearForm<>(one.equalTo().constant().negated(), less), Rel.EQ))));
        }
        return !said ? null : cases.size() == 1 ? cases.getFirst()
                : new LawProposition.Any<>(cases);
    }

    /** {@code where}, over arguments of the types {@code takes}, with each membership in it said
     *  as the operation that answers it of a container of that kind. */
    private static LawProposition<ArgumentRef> inItsWords(Stdlib stdlib, List<Type> takes,
                                                         LawProposition<ArgumentRef> where,
                                                         List<OperationFacts.Declared>
                                                                 memberships) {
        return switch (where) {
            case LawProposition.All<ArgumentRef>(var parts) -> new LawProposition.All<>(
                    parts.stream().map(part -> inItsWords(stdlib, takes, part, memberships))
                            .toList());
            case LawProposition.Any<ArgumentRef>(var parts) -> new LawProposition.Any<>(
                    parts.stream().map(part -> inItsWords(stdlib, takes, part, memberships))
                            .toList());
            case LawProposition.SomeElement<ArgumentRef>(ArgumentRef container,
                    LawProposition.Same<ArgumentRef>(LawSubject<ArgumentRef> named,
                            LawSubject.Argument<ArgumentRef>(ArgumentRef value), boolean alike),
                    boolean some) when alike && namesAnElementOf(named, container) != null
                    && container instanceof ArgumentRef.At(int at) -> {
                for (OperationFacts.Declared membership : memberships) {
                    LawProposition.SomeElement<ArgumentRef> says = membershipOf(membership);
                    if (namesAnElementOf(((LawProposition.Same<ArgumentRef>) says.ofTheElement())
                                    .one(), says.container())
                                    == namesAnElementOf(named, container)
                            && says.container() instanceof ArgumentRef.At(int its)
                            && sameKind(takes.get(at), declaredSignature(stdlib,
                                    membership.operation()).params().get(its))) {
                        LawProposition<ArgumentRef> answered = answeredTrue(stdlib,
                                membership.operation(), says, container, value);
                        yield some ? answered : answered.denied();
                    }
                }
                yield where;
            }
            case LawProposition.Always<ArgumentRef> _, LawProposition.Observed<ArgumentRef> _,
                 LawProposition.Compared<ArgumentRef> _, LawProposition.SomeElement<ArgumentRef> _,
                 LawProposition.Same<ArgumentRef> _ -> where;
        };
    }

    /** Whether {@code a} and {@code b} are containers of one kind: both lists, both sets, or both
     *  maps. */
    private static boolean sameKind(Type a, Type b) {
        return (a instanceof Type.ListOf && b instanceof Type.ListOf)
                || (a instanceof Type.SetOf && b instanceof Type.SetOf)
                || (a instanceof Type.MapOf && b instanceof Type.MapOf);
    }

    /** {@code operation}, whose truth law is {@code says}, answering true handed
     *  {@code container} and {@code value} where it takes them. */
    private static LawProposition<ArgumentRef> answeredTrue(Stdlib stdlib, ValueName operation,
            LawProposition.SomeElement<ArgumentRef> says, ArgumentRef container,
            ArgumentRef value) {
        int arity = declaredSignature(stdlib, operation).params().size();
        List<LawSubject<ArgumentRef>> handed = new ArrayList<>();
        for (int at = 0; at < arity; at++) {
            ArgumentRef here = new ArgumentRef.At(at);
            handed.add(new LawSubject.Argument<>(here.equals(says.container()) ? container
                    : here.equals(heldIn(says)) ? value : here));
        }
        return new LawProposition.Observed<>(new LawSubject.AnswerOf<>(
                theLibraryOperation(operation), handed),
                new SideAnswered(AnswerAspect.TRUTH, true));
    }

    /** One fact held to the declaration it is about. No default: a kind of fact added is a kind
     *  this has to say how to hold and what it comes to, rather than one that passes through
     *  unchecked because nothing here mentions it. */
    private static BoundOperationFact bind(Stdlib stdlib, CompleteSignature declaration,
                                           OperationFact fact) {
        DeclaredOperation operation = declaration.declaring();
        return switch (fact) {
            case OperationFact.AnswersAFormOfItsArguments answers ->
                    new BoundOperationFact.AnswersAFormOfItsArguments(operation,
                            holdAFormOfItsArguments(declaration, answers.form()));
            // Both arguments, because which is the greater and which the lesser are one
            // statement and a signature could disagree with either half.
            case OperationFact.StatesTheOrderOfItsArguments states ->
                    new BoundOperationFact.StatesTheOrderOfItsArguments(operation,
                            holdToTheDeclaration(declaration, states.order().greater(), null,
                                    TypeRequirement.ANY,
                                    "the argument a positive answer names as greater"),
                            holdToTheDeclaration(declaration, states.order().lesser(), null,
                                    TypeRequirement.ANY,
                                    "the argument a positive answer names as lesser"));
            case OperationFact.ShiftsBy shifts -> holdShift(stdlib, declaration, shifts);
            case OperationFact.CountsWholeUnitsBetween counts ->
                    holdCountOfWholeUnits(declaration, counts);
            case OperationFact.BoundsItsResult bounded ->
                    new BoundOperationFact.BoundsItsResult(operation,
                            holdBound(declaration, bounded.bound()));
            case OperationFact.BuildsItsResultFrom builds ->
                    new BoundOperationFact.BuildsItsResultFrom(operation,
                            holdBuilding(declaration, builds));
            case OperationFact.ElementsComeFrom comes ->
                    new BoundOperationFact.ElementsComeFrom(operation,
                            holdElementsComeFrom(declaration, comes));
            case OperationFact.HoldsTheImageOfEveryElement holds ->
                    new BoundOperationFact.HoldsTheImageOfEveryElement(operation,
                            holdTheImage(declaration, holds));
            case OperationFact.HoldsThePiecesOf pieces -> {
                holdTheResultToTheDeclaration(declaration, TypeRequirement.CONTAINER,
                        "the pieces a string falls into");
                yield new BoundOperationFact.HoldsThePiecesOf(operation,
                        holdToTheDeclaration(declaration, pieces.separator(), null,
                                TypeRequirement.TEXT, "where the pieces are parted"),
                        holdToTheDeclaration(declaration, pieces.string(), null,
                                TypeRequirement.TEXT, "the string that falls into pieces"));
            }
            // A key kept is the same key, so the answer is a map keyed by what the map named is.
            case OperationFact.KeepsTheKeysOf kept -> {
                DeclaredArgument map = holdToTheDeclaration(declaration, kept.map(),
                        new ArgumentRef.TheContainer(), TypeRequirement.KEYED,
                        "the map the keys were kept from");
                holdTheAnswerTo(declaration, map, Type::keyOf, Type::keyOf,
                        "a map keyed by the keys of that map");
                yield new BoundOperationFact.KeepsTheKeysOf(operation, map,
                        slots(stdlib, declaration, kept.states(
                                theLibraryOperation(operation.operation()),
                                declaration.params().size()), false));
            }
            case OperationFact.HasALaw stated -> {
                // A law beside a body is a second account of what the body does: what is stated
                // of an operation the library writes is a lemma, proved against the body.
                if (stdlib.helpers().containsKey(theLibraryOperation(operation.operation()))) {
                    throw new IllegalStateException(operation.operation() + " is written in the"
                            + " language, and a law of it is declared beside its body: state it"
                            + " as a lemma, to be proved against the body");
                }
                yield holdLaw(declaration, operation, stated.law());
            }
            case OperationFact.LeavesUnsaid unsaid -> holdUnsaid(declaration, operation, unsaid);
            case OperationFact.IsALemma lemma -> {
                if (!stdlib.helpers().containsKey(theLibraryOperation(operation.operation()))) {
                    throw new IllegalStateException(operation.operation() + " is a kernel, with no"
                            + " body for a lemma to be proved against: what is stated of it is a"
                            + " law");
                }
                yield new BoundOperationFact.HasALemma(operation,
                        ((BoundOperationFact.HasALaw) holdLaw(declaration, operation,
                                lemma.states())).law(),
                        lemma.carries().stream().map(clause ->
                                slots(stdlib, declaration, clause, true)).toList());
            }
            case OperationFact.IsRelatedInALemma lemma -> {
                if (!stdlib.helpers().containsKey(theLibraryOperation(operation.operation()))) {
                    throw new IllegalStateException(operation.operation() + " is a kernel, with no"
                            + " body for a lemma to be proved against: what is stated of it beside"
                            + " other kernels is an axiom");
                }
                yield new BoundOperationFact.HasARelatedLemma(operation,
                        slots(stdlib, declaration, lemma.holds(), false),
                        lemma.carries().stream().map(clause ->
                                slots(stdlib, declaration, clause, true)).toList());
            }
            case OperationFact.IsRelated related -> {
                if (stdlib.intrinsicOf(theLibraryOperation(operation.operation())) == null) {
                    throw new IllegalStateException(operation.operation() + " is written in the"
                            + " language, and what it answers is related to other kernels' answers"
                            + " beside its body: what a body comes to is proved of it");
                }
                yield new BoundOperationFact.IsRelated(operation,
                        slots(stdlib, declaration, related.holds(), false));
            }
            // A list of a part of a map is a list of values of that part's type.
            case OperationFact.ListsAPartOf lists -> {
                DeclaredArgument map = holdToTheDeclaration(declaration, lists.map(),
                        new ArgumentRef.TheContainer(), TypeRequirement.KEYED, "the map listed");
                holdTheAnswerTo(declaration, map, UnaryOperator.identity(),
                        held -> Type.list(partOf(held, lists.part())),
                        "a list of the " + switch (lists.part()) {
                            case KEYS -> "keys";
                            case VALUES -> "values";
                            case ENTRIES -> "entries";
                        } + " of that map");
                yield new BoundOperationFact.ListsAPartOf(operation, map, lists.part());
            }
            // What is no smaller than a container is one: a size is what the two are compared by.
            case OperationFact.ResultIsNoSmallerThan bounded -> {
                // Of anything holding a number of things, a string as much as a container: how many
                // a value holds is what the bound is about.
                holdTheResultToTheDeclaration(declaration, TypeRequirement.SIZED,
                        "what is no smaller than what it was built from");
                yield new BoundOperationFact.ResultIsNoSmallerThan(operation,
                        holdToTheDeclaration(declaration, bounded.container(),
                                new ArgumentRef.TheContainer(), TypeRequirement.SIZED,
                                "what the result is no smaller than"));
            }
            // An order is of a sequence, and of the answer's elements as it is of the source's.
            case OperationFact.KeepsTheOrderOf kept -> {
                holdTheResultToTheDeclaration(declaration, TypeRequirement.CONTAINER,
                        "what keeps the order of what it was built from");
                yield new BoundOperationFact.KeepsTheOrderOf(operation,
                        holdToTheDeclaration(declaration, kept.source(),
                                new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                                "what the order is of"));
            }
            // What a value is put in answers a container like it, and what is put in is one of what
            // such a container holds.
            case OperationFact.PutsAValueIn puts -> {
                if (stdlib.intrinsicOf(theLibraryOperation(operation.operation())) == null) {
                    throw new IllegalStateException(operation.operation() + " is written in the"
                            + " language, and what it puts in is declared beside its body: what a"
                            + " body builds is proved of it");
                }
                DeclaredArgument into = holdToTheDeclaration(declaration, puts.into(), null,
                        TypeRequirement.CONTAINER, "what a value is put in");
                DeclaredArgument value = holdToTheDeclaration(declaration, puts.value(), null,
                        TypeRequirement.ANY, "the value put in");
                holdTheAnswerTo(declaration, into, UnaryOperator.identity(),
                        UnaryOperator.identity(), "the same kind of container");
                holdTheAnswerTo(declaration, value, Type::elementOfAContainer,
                        UnaryOperator.identity(), "a container and one of what it holds");
                yield new BoundOperationFact.PutsAValueIn(operation, value, into);
            }
            case OperationFact.ReadsItsContainer reads ->
                    new BoundOperationFact.ReadsItsContainer(operation,
                            holdToTheDeclaration(declaration, reads.container(),
                                    new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                                    "the container a predicate reads"),
                            reads.through());
            case OperationFact.IsStatedOverAProjection over ->
                    new BoundOperationFact.IsStatedOverAProjection(operation,
                            holdToTheDeclaration(declaration, over.projection(),
                                    new ArgumentRef.TheClosure(), TypeRequirement.CLOSURE,
                                    "the projection a predicate is stated over"));
            // Names no argument, but it does name another operation — and what a reader does
            // with it is write a call of that one where a call of this one stands. So the two
            // declarations are held to each other.
            case OperationFact.MeansTheSameAsASizeOfNought means ->
                    holdSizeEquivalence(stdlib, declaration, means.size());
            // Names nothing beyond the operation it is about, so there is nothing about it to hold
            // to a signature beyond the declaration every fact is held to above. What it comes to
            // bound is the fact about that declaration.
            case OperationFact.StatesItsPredicateOfEveryElement _ ->
                    new BoundOperationFact.StatesItsPredicateOfEveryElement(operation);
            // Stated of the number an operation answers, so an operation that answers none is
            // one the proposition is not about. Waved through, it was a fact anything could
            // carry (#1027).
            case OperationFact.EveryAnswerItCanGiveHasASourceValue _ -> {
                holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                        "what every answer of it has a value for");
                yield new BoundOperationFact.EveryAnswerItCanGiveHasASourceValue(operation);
            }
            case OperationFact.AnswersANumberTakenOfAValueItIsGiven taken ->
                    holdTakenOf(declaration, taken.how());
            case OperationFact.AccumulatesItsContainer accumulates ->
                    new BoundOperationFact.AccumulatesItsContainer(operation,
                            holdAccumulation(declaration, accumulates.container()),
                            accumulates.how());
            case OperationFact.ComputesANumber computes ->
                    new BoundOperationFact.ComputesANumber(operation,
                            holdNumericResult(stdlib, declaration, computes.result()));
            case OperationFact.IsDefinedByCases defined ->
                    new BoundOperationFact.IsDefinedByCases(operation,
                            holdCase(declaration, defined.one()));
        };
    }

    /**
     * Holds one rule to the operation it is about: the argument it names is one the declaration
     * has, and what stands there is what the rule requires. A rule naming a part of something the
     * signature says the operation does not hand is caught by the word itself; one that writes a
     * position the signature already answers is caught here, since two answers to one question are
     * what come apart later.
     *
     * <p><b>The one place a word becomes a position.</b> What {@link ArgumentRef.TheContainer} and
     * {@link ArgumentRef.TheClosure} are positions of is read off the library's own declaration
     * ({@link Combinators}), here and nowhere below: what comes back is a {@link DeclaredArgument},
     * which carries the position, and a reader below has that and no word to resolve.
     */
    static DeclaredArgument holdToTheDeclaration(CompleteSignature declaration, ArgumentRef at,
                                                 ArgumentRef derived, TypeRequirement required,
                                                 String role) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        List<Type> params = declaration.params();
        int position = positionIn(at, library);
        if (position < 0 || position >= params.size()) {
            throw new IllegalStateException(library.qualified() + " takes " + params.size()
                    + " argument(s), and the rule about " + role + " reads argument "
                    + (position + 1));
        }
        Type stands = params.get(position);
        if (!required.admits(stands)) {
            throw new IllegalStateException("argument " + (position + 1) + " of "
                    + library.qualified() + " is " + Type.show(stands) + ", not " + required
                    + "; it is named as " + role);
        }
        if (at instanceof ArgumentRef.At && derived != null
                && Combinators.positionsOf(library) != null
                && positionIn(derived, library) == position) {
            throw new IllegalStateException("the rule about " + role + " for "
                    + library.qualified()
                    + " writes the argument its signature already answers — say which part it is"
                    + " rather than where, so the two cannot come apart");
        }
        return new DeclaredArgument(declaration.declaring(), position, stands);
    }

    /**
     * Which parameter of {@code operation} {@code ref} names.
     *
     * <p>A written position is itself. The two that are named by the part they play are the
     * library's to say, and an operation whose signature hands its closure nothing a container
     * holds has neither — a fact naming one of them there is a fact about an argument that is not
     * there, and it is said rather than answered with a number that would be wrong.
     */
    private static int positionIn(ArgumentRef ref, ValueName operation) {
        return switch (ref) {
            case ArgumentRef.At at -> at.position();
            case ArgumentRef.TheContainer _ -> handing(operation, "the container").containerArg();
            case ArgumentRef.TheClosure _ -> handing(operation, "the closure").closureArg();
            case ArgumentRef.Carried _, ArgumentRef.Walked _, ArgumentRef.Every _ ->
                    throw new IllegalStateException("a fact about " + operation + " names " + ref
                            + ", which is no argument of it: only what a lemma states a walk"
                            + " carries may name one");
        };
    }

    private static ClosurePositions handing(ValueName operation, String part) {
        ClosurePositions handed = Combinators.positionsOf(operation);
        if (handed == null) {
            throw new IllegalStateException("a rule about " + operation + " names " + part
                    + " of what it hands its closure, and its signature puts no closure beside a"
                    + " container");
        }
        return handed;
    }

    /**
     * Holds a declared form to the library: what it answers counts, and so does every argument it
     * is written over.
     *
     * <p>Both ends, because the fact is an equation between them —
     * {@code count(result) = Σ cᵢ·count(argᵢ) + k}. Held of the arguments alone it was half a
     * statement: {@code List.take(n, xs)} declared to answer the number of its first argument
     * passed, that argument being an {@code Int}, while what it answers is a list and has no count
     * for the equation to be about.
     *
     * <p>Counted rather than a number, because that is what the fact says. A date is no number and
     * counts days. And counted is what the discharge check needs of every part to carry a form —
     * a carrier that counts has the coordinate it reasons over — so a form held here is a form
     * that check carries, and it does not ask again.
     */
    private static LinearForm<DeclaredArgument> holdAFormOfItsArguments(
            CompleteSignature declaration, LinearForm<ArgumentRef> form) {
        holdTheResultToTheDeclaration(declaration, TypeRequirement.COUNTED,
                "what a form of its arguments is about");
        LinearForm<DeclaredArgument> bound = LinearForm.constant(form.constant());
        for (Map.Entry<ArgumentRef, ExactRatio> each
                : form.coefs().entrySet()) {
            DeclaredArgument argument = holdToTheDeclaration(declaration, each.getKey(), null,
                    TypeRequirement.COUNTED, "an argument the result is a form of");
            // Numbers a library declares and no model writes, so a sum of them is held.
            bound = bound.plus(LinearForm.weighing(argument, each.getValue()))
                    .orFail("a form a library declares of its arguments has a number no ratio holds");
        }
        return bound;
    }

    /**
     * As {@link #holdToTheDeclaration}, for a rule stating a shift through a measure: the amount is
     * a number, the value shifted is of the type the measure counts, and the measure counts two of
     * what the operation answers. A rule pairing an operation with a measure of something else
     * would state a relation between two values that have none.
     */
    private static BoundOperationFact.ShiftsBy holdShift(Stdlib stdlib,
                                                         CompleteSignature declaration,
                                                         OperationFact.ShiftsBy shift) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        DeclaredArgument amount = holdToTheDeclaration(declaration, shift.amount(), null,
                TypeRequirement.NUMBER, "the amount a shift moves by");
        Stdlib.Entry counts = stdlib.entry(shift.measure());
        if (counts == null) {
            throw new IllegalStateException("the rule about " + library.qualified()
                    + " counts through " + shift.measure().qualified()
                    + ", which the library does not declare");
        }
        List<Type> counted = counts.signature().params();
        if (counted.size() != 2 || !NumericAnswers.isANumber(counts.signature().result())
                || !counted.get(0).equals(declaration.result())
                || !counted.get(1).equals(declaration.result())) {
            throw new IllegalStateException(shift.measure().qualified()
                    + " does not count two of what " + library.qualified()
                    + " answers apart as a number");
        }
        DeclaredArgument moved = holdToTheDeclaration(declaration, shift.of(), null,
                TypeRequirement.ANY, "the value a shift moves from");
        // Not a requirement on the type, which is why it is stated here rather than passed as one.
        // What this asks is that two positions of one signature stand at the same type, and nothing
        // about a type on its own answers that — a requirement able to say it would be one carrying
        // the signature it was written for.
        if (!moved.stands().equals(declaration.result())) {
            throw new IllegalStateException("the value " + library.qualified()
                    + " shifts is " + Type.show(moved.stands()) + " and what it answers is "
                    + Type.show(declaration.result())
                    + ", so what it moves is not what the measure counts");
        }
        return new BoundOperationFact.ShiftsBy(declaration.declaring(),
                declaredSignature(stdlib, shift.measure()).declaring(), moved, amount, shift.per());
    }

    /**
     * As {@link #holdToTheDeclaration}, for a count of whole units between two values: the answer is
     * a number, and what is counted from and to is of one type, since a count of units between two
     * values of different kinds has no steps to count.
     */
    static BoundOperationFact.CountsWholeUnitsBetween holdCountOfWholeUnits(
            CompleteSignature declaration, OperationFact.CountsWholeUnitsBetween counts) {
        holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                "what a count of whole units is");
        // Counted: a unit is a number of steps of the order the values stand on, so the steps
        // between two of them are a whole number, and how far apart two can be is the order's own
        // first value and last. What reads the fact stands on both.
        DeclaredArgument from = holdToTheDeclaration(declaration, counts.from(), null,
                TypeRequirement.COUNTED, "the value the units are counted from");
        DeclaredArgument to = holdToTheDeclaration(declaration, counts.to(), null,
                TypeRequirement.COUNTED, "the value the units are counted to");
        if (!from.stands().equals(to.stands())) {
            throw new IllegalStateException("the units are counted from "
                    + Type.show(from.stands()) + " to " + Type.show(to.stands())
                    + ", which are not steps of one order");
        }
        return new BoundOperationFact.CountsWholeUnitsBetween(declaration.declaring(), from, to,
                counts.perUnit());
    }

    /** As {@link #holdToTheDeclaration}, for the arguments a case names: the ones the number it
     *  answers is written in, and the ones each side of each condition it is reached under is. */
    private static DefinitionCase<DeclaredArgument> holdCase(CompleteSignature declaration,
                                                             DefinitionCase<ArgumentRef> one) {
        holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                "what a case of the definition answers");
        List<ArgumentsStand<DeclaredArgument>> given = new ArrayList<>();
        for (ArgumentsStand<ArgumentRef> stands : one.given()) {
            given.add(new ArgumentsStand<>(holdCaseForm(declaration, stands.left()),
                    stands.rel(), holdCaseForm(declaration, stands.right())));
        }
        return new DefinitionCase<>(holdCaseForm(declaration, one.answers()), given);
    }

    /** {@code form}, each argument it is written in held to the declaration. */
    private static LinearForm<DeclaredArgument> holdCaseForm(CompleteSignature declaration,
                                                             LinearForm<ArgumentRef> form) {
        Map<DeclaredArgument, ExactRatio> held = new LinkedHashMap<>();
        form.coefs().forEach((named, weight) ->
                held.put(holdCaseArgument(declaration, named), weight));
        return new LinearForm<>(form.constant(), held);
    }

    private static DeclaredArgument holdCaseArgument(CompleteSignature declaration,
                                                     ArgumentRef named) {
        return holdToTheDeclaration(declaration, named, null, TypeRequirement.NUMBER,
                "an argument a case of the definition names");
    }

    /** As {@link #holdToTheDeclaration}, for the arguments a bound names: the one the result is
     *  bounded against, and the one a condition on the rule reads. Each is a separate claim about a
     *  separate argument. */
    private static ResultBound<DeclaredArgument> holdBound(CompleteSignature declaration,
                                                           ResultBound<ArgumentRef> bound) {
        holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                "what a bound on the result holds of");
        DeclaredArgument against = bound.against() == null ? null
                : holdBoundArgument(declaration, bound.against());
        ResultBound.Provided<DeclaredArgument> provided = switch (bound.provided()) {
            case ResultBound.Provided.Always<ArgumentRef> _ -> new ResultBound.Provided.Always<>();
            case ResultBound.Provided.ConstantAboveZero<ArgumentRef> constant ->
                    new ResultBound.Provided.ConstantAboveZero<>(
                            holdBoundArgument(declaration, constant.argument()));
            case ResultBound.Provided.ConstantBelowZero<ArgumentRef> constant ->
                    new ResultBound.Provided.ConstantBelowZero<>(
                            holdBoundArgument(declaration, constant.argument()));
        };
        return new ResultBound<>(against, bound.offset(), bound.rel(), provided);
    }

    private static DeclaredArgument holdBoundArgument(CompleteSignature declaration,
                                                      ArgumentRef named) {
        return holdToTheDeclaration(declaration, named, null, TypeRequirement.NUMBER,
                "an argument a bound on the result names");
    }

    /**
     * Holds a building to the library: every argument the lineage names is a container the
     * declaration has.
     *
     * <p>Every argument and not the one source. A lineage whose elements come from more than one
     * place names each of them, and each is a claim about an argument; held for the source alone,
     * a second argument named by an alternative was one nothing had read.
     */
    private static BuiltFrom<DeclaredArgument> holdBuilding(
            CompleteSignature declaration, OperationFact.BuildsItsResultFrom builds) {
        Map<ArgumentRef, DeclaredArgument> held = new HashMap<>();
        BuiltFrom<DeclaredArgument> built = builds.built().withArguments(named ->
                held.computeIfAbsent(named,
                        each -> holdToTheDeclaration(declaration, each,
                                new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                                "the container something is built from")));
        // An answer holding the very elements of an argument holds values of their type. This is
        // what a reader walking back from an element of the answer to the argument relies on.
        DeclaredArgument same = built.holdsTheElementsOf();
        if (same != null) {
            holdTheAnswerTo(declaration, same, Type::elementOfAContainer,
                    Type::elementOfAContainer, "a container of the elements that argument holds");
        }
        // And an answer holding a component of the tuples an argument holds holds values of that
        // component's type.
        ElementLineage.TupleComponent<DeclaredArgument> part = built.componentOfTheElementsOf();
        if (part != null) {
            holdTheAnswerTo(declaration, part.source().argument(), Type::elementOfAContainer,
                    container -> componentOfTheElement(container, part.index()),
                    "a container of the component of the tuples that argument holds");
        }
        built.outputs().forEach(each -> holdWhatTheClosureAnswered(declaration, each.origin()));
        return built;
    }

    /** The type of component {@code index} of the tuples a container holds, or null where it holds
     *  no tuples or they have no such component. */
    private static Type componentOfTheElement(Type container, int index) {
        return Type.elementOfAContainer(container) instanceof Type.TupleOf(var components)
                && index < components.size() ? components.get(index) : null;
    }

    /** Holds the argument whose elements the answer holds an image of to a container the
     *  declaration has, the answer to a container of what the image is, and the closure it says
     *  made them to the signature. */
    private static ElementLineage<DeclaredArgument> holdTheImage(
            CompleteSignature declaration, OperationFact.HoldsTheImageOfEveryElement holds) {
        ElementLineage<DeclaredArgument> held = holds.image()
                .withArguments(named -> holdToTheDeclaration(declaration, named,
                        new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                        "the container whose every element has an image in the answer"));
        if (held instanceof ElementLineage.SameAs<DeclaredArgument> same) {
            holdTheAnswerTo(declaration, same.source().argument(), Type::elementOfAContainer,
                    Type::elementOfAContainer,
                    "a container of the elements that argument holds");
        }
        holdWhatTheClosureAnswered(declaration, held);
        return held;
    }

    /** Holds the argument a lineage of made elements names to a container the declaration has, and
     *  the closure it says made them to the signature. */
    private static ElementLineage<DeclaredArgument> holdElementsComeFrom(
            CompleteSignature declaration, OperationFact.ElementsComeFrom comes) {
        ElementLineage<DeclaredArgument> held = comes.lineage()
                .withArguments(named -> holdToTheDeclaration(declaration, named,
                        new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                        "the container something is made from"));
        holdWhatTheClosureAnswered(declaration, held);
        return held;
    }

    /**
     * Holds a lineage that says an element is what a closure answered, or is inside it, to the
     * signature: the operation hands a closure the elements of the argument the lineage names, and
     * the closure answers what the elements of the result are, or a list or an optional of them.
     *
     * <p>Said of the signature and not of the body, because a kernel has none to prove it of. A
     * lineage nothing here holds to the declaration is a statement about a closure the operation
     * may not take, and what reads it would trace a value back to an argument it was never made
     * from.
     */
    private static void holdWhatTheClosureAnswered(CompleteSignature declaration,
                                                   ElementLineage<DeclaredArgument> lineage) {
        switch (lineage) {
            case ElementLineage.SameAs<DeclaredArgument> _ -> { }
            case ElementLineage.TupleComponent<DeclaredArgument> _ -> { }
            case ElementLineage.ClosureResult<DeclaredArgument> made ->
                    holdTheClosureAnswerTo(declaration, made.source().argument(), false);
            case ElementLineage.InsideClosureResult<DeclaredArgument> inside ->
                    holdTheClosureAnswerTo(declaration, inside.source().argument(), true);
            case ElementLineage.OneOf<DeclaredArgument>(var alternatives) ->
                    alternatives.forEach(each -> holdWhatTheClosureAnswered(declaration, each));
        }
    }

    private static void holdTheClosureAnswerTo(CompleteSignature declaration,
                                               DeclaredArgument container, boolean inside) {
        String name = ((ValueName.Stdlib) declaration.declaring().operation()).qualified();
        ClosurePositions handed = Combinators.positionsOf(declaration.declaring().operation());
        if (handed == null || handed.containerArg() != container.position()) {
            throw new IllegalStateException(name + " is said to answer what a closure made of the"
                    + " elements of argument " + (container.position() + 1) + ", and its signature"
                    + " hands no closure those");
        }
        Type answered = declaration.params().get(handed.closureArg()) instanceof Type.FnOf fn
                ? fn.result() : null;
        Type made = !inside ? answered
                : answered instanceof Type.ListOf(Type element) ? element
                : answered instanceof Type.OptionOf(Type element) ? element : null;
        Type held = Type.elementOf(declaration.result());
        if (made == null || !made.equals(held)) {
            throw new IllegalStateException(name + " answers " + Type.show(declaration.result())
                    + " and its closure answers "
                    + (answered == null ? "nothing" : Type.show(answered)) + ", which are not "
                    + (inside ? "a list or an optional of what the result holds"
                            : "what the result holds"));
        }
    }

    /**
     * As {@link #holdToTheDeclaration}, for the arithmetic an operation computes: it takes as many
     * arguments as the row hands over, and it answers its number where the row says it does.
     *
     * <p>The result position is the half a signature can disagree with silently. A row saying the
     * number arrives in the case carrying {@code Int} is read at an arm, and an arm that never
     * matches is an arm that reports nothing — so a union that gained a case, or lost the one the
     * row names, would leave the operation with a meaning no program reaches and no diagnostic
     * anywhere. Held here, before any call is read.
     */
    private static NumericResult<DeclaredArgument> holdNumericResult(
            Stdlib stdlib, CompleteSignature declaration, NumericResult<ArgumentRef> rule) {
        DeclaredOperation operation = declaration.declaring();
        Type answers = NumericAnswers.in(declaration.result());
        List<Arithmetic.Reads> reads = rule.computes().reads();
        if (declaration.params().size() != reads.size()) {
            throw new IllegalStateException(operation + " takes " + declaration.params().size()
                    + " argument(s), and the arithmetic written for it reads " + reads.size());
        }
        for (int i = 0; i < reads.size(); i++) {
            if (!heldBy(stdlib, reads.get(i), declaration.params().get(i), answers)) {
                throw new IllegalStateException("argument " + (i + 1) + " of " + operation
                        + " is " + Type.show(declaration.params().get(i))
                        + ", which the arithmetic written for it reads as " + reads.get(i));
            }
        }
        switch (rule.at()) {
            case NumericResult.Answered.Directly _ ->
                    holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                            "where the arithmetic it computes is answered");
            case NumericResult.Answered.InTheCaseCarrying(Type carried) -> {
                if (!(declaration.result()
                        instanceof Type.Union(SequencedSet<TypeSymbol> members))) {
                    throw new IllegalStateException(operation + " answers "
                            + Type.show(declaration.result())
                            + ", which has no case for the number it computes to arrive in");
                }
                if (!carried.equals(answers)) {
                    throw new IllegalStateException(operation + " answers no case carrying "
                            + Type.show(carried));
                }
                if (rule.unless() == null) {
                    throw new IllegalStateException(operation + " answers its number as one case"
                            + " of a union, so when the other case comes back is what that case"
                            + " means and is not written down");
                }
                // The condition names no case, so it says what every case that is not the
                // number's says — which is one statement only where there is one such case. A
                // union that gained a third would have an arm establishing a condition it was
                // not taken under, which is a wrong fact rather than a missing one, and nothing
                // downstream could tell: an arm is read the same way whichever case it names.
                // Where a second failure is wanted, the condition is what has to name its case.
                if (members.size() != 2) {
                    throw new IllegalStateException(operation + " answers "
                            + members.size() + " cases, and when it answers no number is"
                            + " written as one condition — which says what one other case"
                            + " means and cannot say what several do");
                }
            }
        }
        NumericResult.TheOtherCaseWhen<DeclaredArgument> unless = rule.unless() == null ? null
                : new NumericResult.TheOtherCaseWhen<>(
                        holdToTheDeclaration(declaration, rule.unless().argument(), null,
                                TypeRequirement.NUMBER, "the argument a failure is decided by"),
                        rule.unless().op(), rule.unless().than());
        return new NumericResult<>(rule.at(), rule.computes(), unless);
    }

    /**
     * Whether the argument declared {@code at} is what the row says that position reads, for an
     * operation answering {@code answered}.
     *
     * <p>Here and not on {@link Arithmetic.Reads}, which says what a position is and stops there.
     * Holding one of those to a declaration is a question about the library, and this is the reader
     * that has the library — the same reader that holds the operation's arity and its result to it.
     *
     * <p>Two of them are answered from the row itself: the number the operation answers is the one
     * its result carries, and a scale is a count. The third is answered from a declaration, because
     * there is nothing about a rounding policy that a type says of itself — and reading it off a
     * name written here would be a second answer to which type it is, which is what ADR-0087 ends.
     */
    private static boolean heldBy(Stdlib stdlib, Arithmetic.Reads reads, Type at, Type answered) {
        return switch (reads) {
            case THE_NUMBER_IT_ANSWERS -> at.equals(answered);
            case A_SCALE -> at == Type.Prim.INT;
            case A_ROUNDING_MODE -> at.equals(theRoundingPolicyTheLibraryDeclares(stdlib));
        };
    }

    /** Which library operation the rounding policy is read off, and where in its arguments. */
    private static final ValueName.Stdlib ROUNDING_POLICY_ANCHOR =
            ValueName.Stdlib.operation("Decimal", "round");

    /** {@code round(scale, mode, d)} — the second of them. */
    private static final int ROUNDING_POLICY_ARGUMENT = 1;

    /**
     * The type the library declares for a rounding policy, taken from the operation that declares
     * one and read as whatever that operation declares there.
     *
     * <p>Whatever it declares there, and never a type this checks against. A rule that said the
     * anchor's argument must be {@code RoundingMode} would be the spelling back again, one operation
     * further along. What is held is that two declarations agree: {@code Decimal.divide} takes at
     * its policy position the type {@code Decimal.round} takes at its own, and either of them
     * drifting alone fails this. Both moving to a new policy type together passes, and should —
     * that is the library being redesigned rather than the table and the library disagreeing.
     *
     * <p>The anchor is a choice and is written down as one. What it is not is a second definition
     * of which type the policy is: the library's declaration remains the only one.
     *
     * @throws IllegalStateException where the anchor no longer declares the argument it is read off
     */
    private static Type theRoundingPolicyTheLibraryDeclares(Stdlib stdlib) {
        List<Type> params = holdTheOperationToTheLibrary(stdlib, ROUNDING_POLICY_ANCHOR)
                .signature().params();
        if (params.size() <= ROUNDING_POLICY_ARGUMENT) {
            throw new IllegalStateException(ROUNDING_POLICY_ANCHOR.qualified() + " takes "
                    + params.size() + " argument(s), and the rounding policy every arithmetic over"
                    + " one is held to is read off argument " + (ROUNDING_POLICY_ARGUMENT + 1)
                    + " of it");
        }
        return params.get(ROUNDING_POLICY_ARGUMENT);
    }

    /**
     * {@code statement} in the words of a walk ({@link Slot}): each argument it names held to the
     * declaration as a place, each part of a walk taken as it is — where {@code ofAWalk}, and
     * refused otherwise — and every other operation it names an answer of held to the library.
     */
    private static LawProposition<Slot> slots(Stdlib stdlib, CompleteSignature declaration,
                                              LawProposition<ArgumentRef> statement,
                                              boolean ofAWalk) {
        answersNamedIn(stdlib, statement);
        return ByPlace.proposition(statement, ref -> switch (ref) {
            case ArgumentRef.At _, ArgumentRef.TheContainer _, ArgumentRef.TheClosure _ ->
                    new Slot.Place(holdToTheDeclaration(declaration, ref, null,
                            TypeRequirement.ANY, "what a statement about it names").position());
            case ArgumentRef.Every(int which) -> new Slot.Every(which);
            case ArgumentRef.Carried(List<Integer> path) when ofAWalk -> new Slot.Carried(path);
            case ArgumentRef.Walked _ when ofAWalk -> new Slot.Walked();
            case ArgumentRef.Carried _, ArgumentRef.Walked _ -> throw new IllegalStateException(
                    "what is stated of " + declaration.declaring().operation() + " beside other"
                            + " kernels names " + ref + ", a part of a walk it has none of");
        });
    }

    /** Holds every other operation {@code statement} names an answer of to the library: one it
     *  declares, handed as many arguments as it takes. */
    private static void answersNamedIn(Stdlib stdlib, LawProposition<ArgumentRef> statement) {
        switch (statement) {
            case LawProposition.Always<ArgumentRef> _ -> { }
            case LawProposition.All<ArgumentRef>(var parts) ->
                    parts.forEach(part -> answersNamedIn(stdlib, part));
            case LawProposition.Any<ArgumentRef>(var parts) ->
                    parts.forEach(part -> answersNamedIn(stdlib, part));
            case LawProposition.Observed<ArgumentRef>(LawSubject<ArgumentRef> of, var _) ->
                    answersNamedIn(stdlib, of);
            case LawProposition.Compared<ArgumentRef>(var form, var _) ->
                    form.coefs().keySet().forEach(number -> {
                        switch (number) {
                            case LawNumber.SizeOf<ArgumentRef>(LawSubject<ArgumentRef> of) ->
                                    answersNamedIn(stdlib, of);
                            case LawNumber.CodePointsOf<ArgumentRef>(
                                    LawSubject<ArgumentRef> of, var _) ->
                                    answersNamedIn(stdlib, of);
                            case LawNumber.HowManyMeet<ArgumentRef>(var _, var ofTheElement) ->
                                    answersNamedIn(stdlib, ofTheElement);
                            case LawNumber.HowManyDifferent<ArgumentRef>(var _, var ofTheElement)
                                    -> answersNamedIn(stdlib, ofTheElement);
                            case LawNumber.SumOver<ArgumentRef>(var _, var ofTheElement) ->
                                    answersNamedIn(stdlib, new LawProposition.Compared<>(
                                            LinearForm.atom(ofTheElement), Rel.EQ));
                            case LawNumber.AnArgument<ArgumentRef> _ -> { }
                        }
                    });
            case LawProposition.SomeElement<ArgumentRef>(var _, var ofTheElement, var _) ->
                    answersNamedIn(stdlib, ofTheElement);
            case LawProposition.Same<ArgumentRef>(var one, var other, var _) -> {
                answersNamedIn(stdlib, one);
                answersNamedIn(stdlib, other);
            }
        }
    }

    private static void answersNamedIn(Stdlib stdlib, LawSubject<ArgumentRef> subject) {
        if (subject instanceof LawSubject.AnswerOf<ArgumentRef>(var operation, var args)) {
            Stdlib.Entry entry = holdTheOperationToTheLibrary(stdlib, operation);
            if (entry.signature().params().size() != args.size()) {
                throw new IllegalStateException("a statement names what " + operation
                        + " answers handed " + args.size() + " argument(s), and it takes "
                        + entry.signature().params().size());
            }
            args.forEach(arg -> answersNamedIn(stdlib, arg));
        }
    }

    /** The library operation {@code operation} names. Every fact is declared of one, so the name
     *  says which library and which operation rather than a spelling a reader would have to take
     *  apart.
     *
     *  @throws IllegalStateException where the name is no library operation. */
    static ValueName.Stdlib.Operation theLibraryOperation(ValueName operation) {
        if (!(operation instanceof ValueName.Stdlib.Operation library)) {
            throw new IllegalStateException("a fact is declared of " + operation
                    + ", which is not a library operation");
        }
        return library;
    }

    /**
     * The library's declaration of {@code operation}, or a build that does not start.
     *
     * <p>What every fact owes, whatever else it says. A fact is a proposition about an operation,
     * so an operation the library does not have is a fact about nothing — and that is true of a
     * fact naming no argument as much as of one that names three.
     */
    static Stdlib.Entry holdTheOperationToTheLibrary(Stdlib stdlib, ValueName operation) {
        ValueName.Stdlib.Operation library = theLibraryOperation(operation);
        Stdlib.Entry entry = stdlib.entry(library);
        if (entry == null) {
            throw new IllegalStateException("a fact is declared of " + library.qualified()
                    + ", which the library does not declare");
        }
        return entry;
    }

    /** The library's declaration of {@code operation}, read whole. */
    static CompleteSignature declaredSignature(Stdlib stdlib, ValueName operation) {
        Stdlib.Entry entry = holdTheOperationToTheLibrary(stdlib, operation);
        return CompleteSignature.ofDeclaration(operation, entry.signature().params(),
                entry.signature().result());
    }

    /**
     * Holds an emptiness check and the size it is said to mean to each other's declarations, and
     * answers with the two as the library declares them.
     *
     * <p>What a reader does with this fact is write the second call where the first stands, keeping
     * the arguments. So what has to hold is that the arguments the first takes are the ones the
     * second takes, and that the two answer the kinds of thing the rewrite turns into each other: a
     * truth on one side, a number to compare against nought on the other. Two operations of one
     * argument each is not enough — a check on strings and a length of lists agree on how many
     * arguments they take and on nothing else.
     */
    private static BoundOperationFact.MeansTheSameAsASizeOfNought holdSizeEquivalence(
            Stdlib stdlib, CompleteSignature asks, ValueName size) {
        ValueName operation = asks.declaring().operation();
        CompleteSignature counts = declaredSignature(stdlib, size);
        if (asks.params().size() != 1 || asks.result() != Type.BOOL) {
            throw new IllegalStateException(theLibraryOperation(operation).qualified()
                    + " is declared to say whether one container is empty, and it takes "
                    + asks.params().size() + " argument(s) and answers "
                    + Type.show(asks.result()));
        }
        if (counts.params().size() != 1 || counts.result() != Type.INT) {
            throw new IllegalStateException(theLibraryOperation(size).qualified()
                    + " is named as the size " + theLibraryOperation(operation).qualified()
                    + " means, and it takes " + counts.params().size()
                    + " argument(s) and answers " + Type.show(counts.result()));
        }
        if (!sameShape(asks.params().get(0), counts.params().get(0),
                new HashMap<>(), new HashMap<>())) {
            throw new IllegalStateException(theLibraryOperation(operation).qualified() + " asks of "
                    + Type.show(asks.params().get(0)) + " and "
                    + theLibraryOperation(size).qualified() + " counts "
                    + Type.show(counts.params().get(0))
                    + ", so a call of the first is no call of the second");
        }
        return new BoundOperationFact.MeansTheSameAsASizeOfNought(asks.declaring(),
                counts.declaring(), new DeclaredArgument(asks.declaring(), 0,
                        asks.params().getFirst()));
    }

    /**
     * Whether the two are the same shape, telling type variables apart only by where they stand.
     *
     * <p>{@code List<'a>} and {@code List<'b>} are one shape and {@code List<'a>} and
     * {@code List<Int>} are not, which is what a rewrite between two declarations needs and what
     * unifying them does not answer: those two unify, by deciding that {@code 'a} is {@code Int},
     * and a rewrite is not free to decide anything. The pairing is carried both ways so that two
     * variables on one side cannot both stand for one on the other.
     */
    private static boolean sameShape(Type left, Type right, Map<String, String> paired,
                                     Map<String, String> back) {
        // A variable of an application, which no declaration holds: this compares what two
        // declarations state. One arriving here is a caller having handed over something else, and
        // answering "a different shape" would report that as the two operations disagreeing.
        if (left instanceof Type.MetaVar || right instanceof Type.MetaVar) {
            throw new IllegalStateException("a declared signature is being compared with "
                    + Type.show(left instanceof Type.MetaVar ? left : right)
                    + ", which belongs to an application rather than to a declaration");
        }
        return switch (left) {
            case Type.Var l when right instanceof Type.Var r ->
                    r.name().equals(paired.computeIfAbsent(l.name(), _ -> r.name()))
                            && l.name().equals(back.computeIfAbsent(r.name(), _ -> l.name()));
            case Type.ListOf l when right instanceof Type.ListOf r ->
                    sameShape(l.element(), r.element(), paired, back);
            case Type.SetOf l when right instanceof Type.SetOf r ->
                    sameShape(l.element(), r.element(), paired, back);
            case Type.OptionOf l when right instanceof Type.OptionOf r ->
                    sameShape(l.element(), r.element(), paired, back);
            case Type.MapOf l when right instanceof Type.MapOf r ->
                    sameShape(l.key(), r.key(), paired, back)
                            && sameShape(l.value(), r.value(), paired, back);
            case Type.FnOf l when right instanceof Type.FnOf r ->
                    sameShapes(l.params(), r.params(), paired, back)
                            && sameShape(l.result(), r.result(), paired, back);
            case Type.TupleOf l when right instanceof Type.TupleOf r ->
                    sameShapes(l.elements(), r.elements(), paired, back);
            // Everything else a declaration can hold stands for itself: a primitive, a declaration,
            // a union of them, and a variable that did not pair with one above. Being the same
            // shape is being the same type.
            case Type.Leaf _ -> left.equals(right);
            default -> false;
        };
    }

    private static boolean sameShapes(List<Type> left, List<Type> right, Map<String, String> paired,
                                      Map<String, String> back) {
        if (left.size() != right.size()) {
            return false;
        }
        for (int i = 0; i < left.size(); i++) {
            if (!sameShape(left.get(i), right.get(i), paired, back)) {
                return false;
            }
        }
        return true;
    }

    /**
     * That what the operation answers holds, where {@code answered} reads it, values of the type
     * {@code given} reads off the argument the fact names — or refused where it does not.
     *
     * <p>A fact relating the answer to an argument states that relation of the two, and holding
     * each position to a requirement of its own says nothing about it: a list and a map pass every
     * such requirement and are related in no way. So the relation is asked of the pair, by reading
     * the same kind of thing off each — what a container holds, the key a map files it under — and
     * comparing them. Where either has no such part, the two are not related as the fact says.
     */
    private static void holdTheAnswerTo(CompleteSignature declaration, DeclaredArgument argument,
                                        UnaryOperator<Type> answered, UnaryOperator<Type> given,
                                        String relation) {
        Type ofTheAnswer = answered.apply(declaration.result());
        Type ofTheArgument = given.apply(argument.stands());
        if (ofTheAnswer == null || !ofTheAnswer.equals(ofTheArgument)) {
            throw new IllegalStateException("what "
                    + ((ValueName.Stdlib) declaration.declaring().operation()).qualified()
                    + " answers is " + Type.show(declaration.result()) + " and argument "
                    + (argument.position() + 1) + " is " + Type.show(argument.stands())
                    + ", which are not " + relation);
        }
    }

    /**
     * The type {@code part} of a map of type {@code map} is, one of which a list of that part holds.
     *
     * <p>Exhaustive over the parts, with no {@code default}: a part added is one this has to say the
     * type of before a fact naming it can be held.
     */
    private static Type partOf(Type map, MapPart part) {
        return switch (part) {
            case KEYS -> Type.keyOf(map);
            case VALUES -> Type.elementOf(map);
            case ENTRIES -> Type.tuple(List.of(Type.keyOf(map), Type.elementOf(map)));
        };
    }

    /**
     * Holds what a fact says of the result to the declaration.
     *
     * <p>Beside {@link #holdToTheDeclaration} and for the half it cannot reach. That one names an
     * argument, so a fact whose proposition mentions the result had nothing to say it with, and
     * each kind that needed the result said it its own way or not at all. Improvising a check per
     * kind defaults to omitting it.
     *
     * <p>Which requirement is the caller's, since what a fact says of the result is the fact's. A
     * form is about a count and a bound about a number, and the difference between those two is a
     * difference between the propositions and not between two ways of holding one.
     */
    private static void holdTheResultToTheDeclaration(CompleteSignature declaration,
                                                      TypeRequirement required, String role) {
        Type result = declaration.result();
        if (!required.admits(result)) {
            throw new IllegalStateException("what "
                    + ((ValueName.Stdlib) declaration.declaring().operation()).qualified()
                    + " answers is " + Type.show(result) + ", not " + required
                    + "; it is named as " + role);
        }
    }

    /**
     * Holds a declared account of what an operation takes of a value it is given to the operation:
     * it takes at least one value, since what such a term is read off is a location and a term
     * names one path; and it answers a number, since a boundary is drawn on one.
     *
     * <p>The number is taken of the first argument. Whether an operation takes others is not what
     * settles such an account: what stands at them may decide which number of the first is taken,
     * and a taking whose arguments say is read where a call is read rather than here.
     *
     * <p>Two of the four things such an account is held to, the two that are about this fact and
     * this declaration alone. The other two are about the operation — that its number is read by
     * one representation, and that what it is taken of is the shape the account is written for —
     * and are asked once every fact is bound ({@link #holdEachNumberToOneReading}), in that order:
     * an account that does not fit the operation is still an account of a number some other
     * representation may already read, and asked the other way round the exclusivity would be
     * reachable only through accounts that happen to fit.
     */
    private static BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven holdTakenOf(
            CompleteSignature declaration, TakenAs how) {
        String named = ((ValueName.Stdlib) declaration.declaring().operation()).qualified();
        if (declaration.params().isEmpty()) {
            throw new IllegalStateException(named + " takes no arguments, and a number taken of a"
                    + " value an operation is given is taken of one it was given");
        }
        // A number and not a number at one case of a union. A term names one path and stands for
        // what the operation answered there, and what an operation answering `Int | NotANumber`
        // answers at that path is the union — which case it is in is a question a declared account
        // has no room for. An operation that reports a case may still be read as a term of its
        // number, and where that holds is a fact about a call rather than about the operation: the
        // account for one is derived where the call's own arguments are known
        // ({@link BoundOperationFacts#takenAs(ValueName, TakenArguments)}), not declared here.
        holdTheResultToTheDeclaration(declaration, TypeRequirement.NUMBER,
                "what a term of its answer is about");
        // The one value, as the declaration has it, carried so that what the account is held to
        // fit is read off the bound fact and not off the declaration a second time.
        DeclaredArgument of = holdToTheDeclaration(declaration, new ArgumentRef.At(0), null,
                TypeRequirement.ANY, "the value a number is taken of");
        return new BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven(
                declaration.declaring(), of, declaration.result(), how);
    }

    /**
     * Holds every operation the library declares to having its number read by at most one
     * representation, and then each account of a number taken of one value to fitting what the
     * operation takes.
     *
     * <p>Asked of the bound facts together and after every one is bound, because the first is a
     * claim about the set: an account declared beside a form is two readings whichever was written
     * first. Asked as "is there already a form, an arithmetic, a body", it is one condition per
     * representation there is, so a fourth has to be named in each of them; asked as how many
     * readings the operation has ({@link NumericReadings}), a representation added is refused
     * against every existing one without being paired with any of them.
     *
     * <p><b>Over the library's operations, and not over the facts of one kind.</b> Two readings of
     * one number are an invalid definition of the operation whichever two they are — a form beside
     * an arithmetic, a walk that adds beside a form — so the population the claim is about is every
     * operation there is, and a walk that started from the accounts of one kind would hold only
     * the pairs that kind is half of. What is refused here is what
     * {@link NumericReadings.Resolution.Multiple} is defined to be, before any reader can meet it.
     *
     * <p>The shape second, since a shape that does not fit is a fact about one account, and the
     * exclusivity is a fact about the operation whatever account was written for it.
     */
    private static void holdEachNumberToOneReading(Stdlib stdlib, BoundOperationFacts facts) {
        for (ValueName.Stdlib.Operation operation : stdlib.entries().keySet()) {
            NumericReadings.Resolution read = NumericReadings.resolve(stdlib, facts, operation);
            if (read instanceof NumericReadings.Resolution.Multiple) {
                throw new IllegalStateException("the number " + operation.qualified()
                        + " answers is read as " + NumericReadings.describe(read)
                        + ", and one numeric call is read by one representation — which of them a"
                        + " report showed would be whichever reader arrived");
            }
        }
        for (BoundOperationFact fact : facts.all()) {
            if (!(fact instanceof BoundOperationFact.AnswersANumberTakenOfAValueItIsGiven
                    taken)) {
                continue;
            }
            // What it takes it of is the shape the account is written for — a count is taken of
            // something that holds things, a magnitude of the operation's own kind of number.
            // Read off the bound fact, which carries the one argument and the answer as the
            // declaration had them.
            Type source = taken.of().stands();
            if (!taken.how().takenOf(source, taken.answers())) {
                throw new IllegalStateException(theLibraryOperation(taken.operation().operation())
                        .qualified() + " is declared to answer "
                        + taken.how().getClass().getSimpleName() + " of a " + Type.show(source)
                        + ", which is not what that is taken of");
            }
        }
    }

    /**
     * Holds an accumulation to the library: the argument it names holds elements, and they are of
     * the type the operation answers.
     *
     * <p>Both halves, because an accumulation carries what it has so far in the answer's own type.
     * A step over what it has and an element is written over two values of one type, so an argument
     * whose elements are something else is one this walk could not be over, and the identity it
     * starts from would be a value of a type nothing here names.
     *
     * <p>Which argument is named rather than searched for. A signature says of as many arguments as
     * fit that they could be the one, and an operation given two containers of what it answers has
     * a signature admitting two walks; the fact says which, and this says whether the signature
     * bears it out.
     */
    private static DeclaredArgument holdAccumulation(CompleteSignature declaration,
                                                     ArgumentRef container) {
        DeclaredArgument walked = holdToTheDeclaration(declaration, container, null,
                TypeRequirement.CONTAINER, "the container it accumulates");
        Type answers = declaration.result();
        Type element = Type.elementOfAContainer(walked.stands());
        if (!element.equals(answers)) {
            throw new IllegalStateException(
                    ((ValueName.Stdlib) declaration.declaring().operation()).qualified()
                    + " is declared to accumulate a container of " + Type.show(element)
                    + " and answers " + Type.show(answers)
                    + ", and a walk carries what it has so far in the type it answers");
        }
        return walked;
    }

    private OperationFactBinder() {}


    /**
     * A law, held to the declaration on every argument and every side it names.
     *
     * <p>Each, because a law read on the wrong side is a wrong statement and not a weaker one. A
     * filterMap read as though its closure answered a truth would be carried back to a rule about
     * the closure's answer holding, which it has no truth to do, and a reader would state of the
     * input what the model never said. So what the answer is observed on is a side the answer has,
     * an argument observed is one that has that side, a number is a number, and what is counted or
     * quantified over is a container.
     *
     * <p>An element is named only inside a statement about some element of its container, and a
     * container is not quantified inside itself: the element would be two elements under one name.
     * What the closure answers is named only of an element of the container the signature says the
     * closure is handed ({@link Combinator}).
     */
    static BoundOperationFact holdLaw(CompleteSignature declaration, DeclaredOperation operation,
                                      OperationLaw<ArgumentRef> law) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        return new BoundOperationFact.HasALaw(operation, switch (law) {
            case OperationLaw.Observation<ArgumentRef> observation -> {
                holdTheSide(observation.aspect(), declaration.result(),
                        "what " + library.qualified() + " answers");
                yield new OperationLaw.Observation<>(observation.aspect(),
                        lawProposition(declaration, observation.equivalentTo(), List.of()));
            }
            case OperationLaw.Size<ArgumentRef> size -> {
                holdTheSide(AnswerAspect.EMPTINESS, declaration.result(),
                        "what " + library.qualified() + " answers as many of");
                yield new OperationLaw.Size<>(size.cases().stream()
                        .map(each -> new OperationLaw.Size.Case<>(
                                lawProposition(declaration, each.where(), List.of()),
                                lawForm(declaration, each.equalTo(), List.of())))
                        .toList());
            }
        }, List.of());
    }

    /** That {@code observed} of the operation's answer is closed, held to a side the answer has. */
    static BoundOperationFact holdUnsaid(CompleteSignature declaration, DeclaredOperation operation,
                                        OperationFact.LeavesUnsaid unsaid) {
        String what = "what " + ((ValueName.Stdlib) declaration.declaring().operation()).qualified()
                + " answers";
        switch (unsaid.observed()) {
            case TRUTH -> holdTheSide(AnswerAspect.TRUTH, declaration.result(), what);
            case EMPTINESS, SIZE -> holdTheSide(AnswerAspect.EMPTINESS, declaration.result(), what);
            case PRESENCE -> holdTheSide(AnswerAspect.PRESENCE, declaration.result(), what);
        }
        return new BoundOperationFact.LeavesUnsaid(operation, unsaid.observed(), unsaid.why());
    }

    /** Whether a value of {@code type} has {@code aspect} to come out on. */
    static boolean hasTheSide(AnswerAspect aspect, Type type) {
        return switch (aspect) {
            case TRUTH -> Type.BOOL.equals(type);
            case EMPTINESS -> Type.elementOfAContainer(type) != null || Type.STRING.equals(type);
            case PRESENCE -> type instanceof Type.OptionOf;
        };
    }

    /** Refuses {@code aspect} where {@code answers} has no such side. */
    private static void holdTheSide(AnswerAspect aspect, Type answers, String what) {
        if (!hasTheSide(aspect, answers)) {
            throw new IllegalStateException(what + " is " + Type.show(answers)
                    + ", which has no " + aspect + " to come out on");
        }
    }

    /**
     * {@code p}, a law of the operation {@code declaration} declares, with every argument it names
     * held to that declaration — inside statements about some element of each of {@code over}.
     */
    private static LawProposition<DeclaredArgument> lawProposition(
            CompleteSignature declaration, LawProposition<ArgumentRef> p,
            List<DeclaredArgument> over) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        return switch (p) {
            case LawProposition.Always<ArgumentRef>(boolean holds) ->
                    new LawProposition.Always<>(holds);
            case LawProposition.All<ArgumentRef> all -> new LawProposition.All<>(all.parts()
                    .stream().map(part -> lawProposition(declaration, part, over)).toList());
            case LawProposition.Any<ArgumentRef> any -> new LawProposition.Any<>(any.parts()
                    .stream().map(part -> lawProposition(declaration, part, over)).toList());
            case LawProposition.Observed<ArgumentRef> observed -> {
                LawSubject<DeclaredArgument> of = lawSubject(declaration, observed.of(), over);
                holdTheSide(observed.side().aspect(), typeOf(of),
                        "what a law of " + library.qualified() + " observes");
                yield new LawProposition.Observed<>(of, observed.side());
            }
            case LawProposition.Compared<ArgumentRef> compared ->
                    new LawProposition.Compared<>(lawForm(declaration, compared.form(), over),
                            compared.states());
            case LawProposition.SomeElement<ArgumentRef> some -> {
                DeclaredArgument container = lawContainer(declaration, some.container(), over);
                yield new LawProposition.SomeElement<>(container, lawProposition(declaration,
                        some.ofTheElement(), within(over, container)), some.holds());
            }
            case LawProposition.Same<ArgumentRef> same -> {
                LawSubject<DeclaredArgument> one = lawSubject(declaration, same.one(), over);
                LawSubject<DeclaredArgument> other = lawSubject(declaration, same.other(), over);
                if (!typeOf(one).equals(typeOf(other))) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " asks whether " + Type.show(typeOf(one)) + " and "
                            + Type.show(typeOf(other)) + " are one value");
                }
                yield new LawProposition.Same<>(one, other, same.holds());
            }
        };
    }

    /** A number of the arguments a law states, held as {@link #lawProposition} holds a law. */
    private static LinearForm<LawNumber<DeclaredArgument>> lawForm(
            CompleteSignature declaration, LinearForm<LawNumber<ArgumentRef>> form,
            List<DeclaredArgument> over) {
        Map<LawNumber<DeclaredArgument>, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((atom, coef) -> coefs.put(lawNumber(declaration, atom, over), coef));
        return new LinearForm<>(form.constant(), coefs);
    }

    private static LawNumber<DeclaredArgument> lawNumber(CompleteSignature declaration,
                                                         LawNumber<ArgumentRef> atom,
                                                         List<DeclaredArgument> over) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        return switch (atom) {
            case LawNumber.AnArgument<ArgumentRef>(ArgumentRef at) ->
                    new LawNumber.AnArgument<>(holdToTheDeclaration(declaration, at,
                            new ArgumentRef.TheContainer(), TypeRequirement.NUMBER,
                            "a number a law of it states something of"));
            case LawNumber.SizeOf<ArgumentRef>(LawSubject<ArgumentRef> of) -> {
                LawSubject<DeclaredArgument> sized = lawSubject(declaration, of, over);
                holdTheSide(AnswerAspect.EMPTINESS, typeOf(sized),
                        "what a law of " + library.qualified() + " takes the size of");
                yield new LawNumber.SizeOf<>(sized);
            }
            case LawNumber.CodePointsOf<ArgumentRef>(LawSubject<ArgumentRef> of,
                                                     CodePointClass counted) -> {
                LawSubject<DeclaredArgument> counting = lawSubject(declaration, of, over);
                if (!Type.STRING.equals(typeOf(counting))) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " counts the code points of " + counting + ", which is no string");
                }
                yield new LawNumber.CodePointsOf<>(counting, counted);
            }
            case LawNumber.HowManyMeet<ArgumentRef> counted -> {
                DeclaredArgument container = lawContainer(declaration, counted.container(), over);
                yield new LawNumber.HowManyMeet<>(container, lawProposition(declaration,
                        counted.ofTheElement(), within(over, container)));
            }
            case LawNumber.HowManyDifferent<ArgumentRef> different -> {
                DeclaredArgument container = lawContainer(declaration, different.container(),
                        over);
                LawSubject<DeclaredArgument> each = lawSubject(declaration,
                        different.ofTheElement(), within(over, container));
                // Something of each element of that container: the element, its key, or what the
                // closure it is handed answers.
                if (!((each instanceof LawSubject.ElementOf<DeclaredArgument>(var of)
                        && of.equals(container))
                        || (each instanceof LawSubject.KeyOf<DeclaredArgument>(var keyed)
                                && keyed.equals(container))
                        || each instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>)) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " counts the different values of " + each + ", which is nothing"
                            + " of each element of argument " + (container.position() + 1));
                }
                yield new LawNumber.HowManyDifferent<>(container, each);
            }
            case LawNumber.SumOver<ArgumentRef> sum -> {
                DeclaredArgument container = lawContainer(declaration, sum.container(), over);
                yield new LawNumber.SumOver<>(container, lawNumber(declaration,
                        sum.ofTheElement(), within(over, container)));
            }
        };
    }

    private static LawSubject<DeclaredArgument> lawSubject(CompleteSignature declaration,
                                                           LawSubject<ArgumentRef> subject,
                                                           List<DeclaredArgument> over) {
        ValueName.Stdlib library = (ValueName.Stdlib) declaration.declaring().operation();
        return switch (subject) {
            case LawSubject.Argument<ArgumentRef>(ArgumentRef at) ->
                    new LawSubject.Argument<>(holdToTheDeclaration(declaration, at,
                            new ArgumentRef.TheContainer(), TypeRequirement.ANY,
                            "a value a law of it states something of"));
            case LawSubject.ElementOf<ArgumentRef>(ArgumentRef at) -> {
                DeclaredArgument container = holdToTheDeclaration(declaration, at,
                        new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                        "a container a law of it names an element of");
                if (!over.contains(container)) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " names an element of argument " + (container.position() + 1)
                            + " outside a statement about some element of it");
                }
                yield new LawSubject.ElementOf<>(container);
            }
            case LawSubject.WhatTheClosureAnswers<ArgumentRef>(ArgumentRef at) -> {
                ClosurePositions walks = Combinators.positionsOf(library);
                if (walks == null) {
                    throw new IllegalStateException(library.qualified() + " hands no closure"
                            + " the elements of a container, so no law of it names what one"
                            + " answers");
                }
                DeclaredArgument closure = holdToTheDeclaration(declaration, at, null,
                        TypeRequirement.CLOSURE, "the closure a law of it names the answer of");
                DeclaredArgument walked = holdToTheDeclaration(declaration,
                        new ArgumentRef.TheContainer(), null, TypeRequirement.CONTAINER,
                        "the container its closure is handed the elements of");
                if (closure.position() != walks.closureArg() || !over.contains(walked)) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " names what its closure answers outside a statement about some"
                            + " element of the container that closure is handed");
                }
                Type.FnOf applied = (Type.FnOf) closure.stands();
                Type element = Type.elementOfAContainer(walked.stands());
                if (!applied.params().get(walks.elementParam()).equals(element)) {
                    throw new IllegalStateException("the closure " + library.qualified()
                            + " applies takes "
                            + Type.show(applied.params().get(walks.elementParam()))
                            + " where an element arrives, and the container holds "
                            + Type.show(element));
                }
                yield new LawSubject.WhatTheClosureAnswers<>(closure);
            }
            case LawSubject.KeyOf<ArgumentRef>(ArgumentRef at) -> {
                DeclaredArgument map = holdToTheDeclaration(declaration, at,
                        new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                        "a map a law of it names the key of an element of");
                if (Type.filedUnder(map.stands()) == null || !over.contains(map)) {
                    throw new IllegalStateException("a law of " + library.qualified()
                            + " names a key of argument " + (map.position() + 1)
                            + " outside a statement about some element of it, or of what is"
                            + " filed under no key");
                }
                yield new LawSubject.KeyOf<>(map);
            }
            // What another operation answers is no argument of this one, and a law says what this
            // one's answer comes to over its own.
            case LawSubject.AnswerOf<ArgumentRef> _ ->
                    throw new IllegalStateException("a law of " + library.qualified() + " names "
                            + subject + ": only a lemma about a body, or what is stated of"
                            + " kernels beside one another, may");
        };
    }

    private static DeclaredArgument lawContainer(CompleteSignature declaration, ArgumentRef at,
                                                 List<DeclaredArgument> over) {
        DeclaredArgument container = holdToTheDeclaration(declaration, at,
                new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                "a container a law of it states something of each element of");
        if (over.contains(container)) {
            throw new IllegalStateException("a law of "
                    + ((ValueName.Stdlib) declaration.declaring().operation()).qualified()
                    + " states something of the elements of argument "
                    + (container.position() + 1) + " inside a statement about one of them");
        }
        return container;
    }

    private static List<DeclaredArgument> within(List<DeclaredArgument> over,
                                                 DeclaredArgument container) {
        List<DeclaredArgument> inside = new ArrayList<>(over);
        inside.add(container);
        return List.copyOf(inside);
    }

    private static Type typeOf(LawSubject<DeclaredArgument> subject) {
        return switch (subject) {
            case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) -> at.stands();
            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                    Type.elementOfAContainer(at.stands());
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) ->
                    ((Type.FnOf) at.stands()).result();
            case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument at) ->
                    Type.filedUnder(at.stands());
            case LawSubject.AnswerOf<DeclaredArgument> _ -> throw new IllegalStateException(
                    "a law names what another operation answers: " + subject);
        };
    }
}
