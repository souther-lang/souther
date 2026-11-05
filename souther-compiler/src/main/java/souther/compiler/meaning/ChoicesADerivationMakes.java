package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The constructs of the model a statement chooses at, read off how the statement was derived: the
 * choices that put alternatives into what it states, which is what its cases are taken apart on.
 *
 * <p>Only choices a construct of the model makes, named as its author wrote them. A choice inside
 * one of the language's own operations is the operation's, and is met as the operation's law or
 * cases at the call; where neither says which kind of choice the author wrote, the construct is not
 * named at all, since a kind guessed from how the derivation is built would be a word for this
 * compiler's steps and not for the model.
 *
 * <p>Each construct once, in the copy it was read in, with the widest choice it was met making —
 * except an {@code if}, whose width is how many times the derivation chooses at it: once on each
 * application of a closure it is read on, and again wherever the derivation reads what an
 * application chose more than once.
 */
public final class ChoicesADerivationMakes {

    private static final ValueName.Stdlib FIND = ValueName.Stdlib.operation("List", "find");
    private static final ValueName.Stdlib FILTER = ValueName.Stdlib.operation("List", "filter");

    private ChoicesADerivationMakes() {
    }

    /** Every construct of the model {@code how} chooses at. */
    public static List<CaseExpansion.Contributing> of(Derivation how) {
        Map<List<Object>, CaseExpansion.Contributing> out = new LinkedHashMap<>();
        Set<Derivation> walked = Collections.newSetFromMap(new IdentityHashMap<>());
        List<Derivation> next = new ArrayList<>(List.of(how));
        while (!next.isEmpty()) {
            Derivation step = next.removeLast();
            if (!walked.add(step)) {
                continue;
            }
            if (step instanceof Derivation.AChoiceAt(var at, var choice)) {
                ModelOccurrence.statedAt(at)
                        .flatMap(construct -> madeAt(construct, at.origin().kind(), choice))
                        .ifPresent(one -> out.merge(List.of(one.construct(), one.kind(),
                                one.operation()), one, ChoicesADerivationMakes::together));
            }
            next.addAll(WrittenLines.premisesOf(step));
        }
        return List.copyOf(out.values());
    }

    /**
     * The choice {@code choice} makes at {@code construct}, written as {@code written}, where it
     * says which kind it is. An {@code if} or a {@code match} is named only where the author wrote
     * one there: the language reads some of its operations as choices of its own, and those are
     * the operation's.
     */
    private static Optional<CaseExpansion.Contributing> madeAt(ModelOccurrence construct,
                                                              SourceConstruct written,
                                                              Derivation choice) {
        return switch (choice) {
            case Derivation.IfThenElse _ when written == SourceConstruct.IF ->
                    Optional.of(new CaseExpansion.Contributing(construct, CaseExpansion.Kind.IF, 1,
                            Optional.empty()));
            case Derivation.MatchArms(var arms) when written == SourceConstruct.MATCH ->
                    Optional.of(new CaseExpansion.Contributing(construct,
                            CaseExpansion.Kind.MATCH, arms.size(), Optional.empty()));
            case Derivation.AnOperationsCases(var operation, var cases) ->
                    Optional.of(new CaseExpansion.Contributing(construct,
                            CaseExpansion.Kind.CASES, cases.size(), Optional.of(operation)));
            case Derivation.ASizeInCases(var call, var cases) ->
                    Optional.of(new CaseExpansion.Contributing(construct,
                            CaseExpansion.Kind.CASES, cases.size(),
                            Optional.of(call.operation())));
            case Derivation.ByALaw(var call, var _, var law) -> {
                CaseExpansion.Kind kind = call.operation().equals(FIND) ? CaseExpansion.Kind.FIND
                        : call.operation().equals(FILTER) ? CaseExpansion.Kind.FILTER : null;
                int elements = elementsWrittenOutIn(law);
                yield kind == null || elements < 1 ? Optional.empty()
                        : Optional.of(new CaseExpansion.Contributing(construct, kind, elements,
                                Optional.of(call.operation())));
            }
            default -> Optional.empty();
        };
    }

    /** How many elements written out the most of any statement over them in {@code law} goes
     *  through, or none where it states nothing over elements written out. */
    private static int elementsWrittenOutIn(Derivation law) {
        int most = 0;
        Set<Derivation> walked = Collections.newSetFromMap(new IdentityHashMap<>());
        List<Derivation> next = new ArrayList<>(List.of(law));
        while (!next.isEmpty()) {
            Derivation step = next.removeLast();
            if (!walked.add(step)) {
                continue;
            }
            if (step instanceof Derivation.OverElementsWrittenOut(var each, var _, var _)) {
                most = Math.max(most, each.size());
            }
            next.addAll(WrittenLines.premisesOf(step));
        }
        return most;
    }

    /** One construct met twice: an {@code if} on one application more, any other choice as wide
     *  as the wider. */
    private static CaseExpansion.Contributing together(CaseExpansion.Contributing one,
                                                       CaseExpansion.Contributing other) {
        int width = one.kind() == CaseExpansion.Kind.IF ? one.width() + other.width()
                : Math.max(one.width(), other.width());
        return new CaseExpansion.Contributing(one.construct(), one.kind(), width,
                one.operation());
    }
}
