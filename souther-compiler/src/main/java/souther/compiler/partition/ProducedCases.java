package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.check.PathReachability;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlPointId;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The cases of a behavior's output that no row could carry, because everything answering with them is
 * behind an arm nothing reaches.
 *
 * <p>Taken away and not counted up. A case a body has no producer for stays owed: that a signature
 * says {@code A | B} and an implementation never answers {@code B} is a gap between the two, and it is
 * the kind of gap a coverage measure is for. What is not a gap is a case something does answer with,
 * at a place the model's own rules prove nothing reaches — nobody can write that row, and asking is
 * asking for work nobody can do.
 *
 * <pre>
 * a reachable producer, or one this cannot read   keep
 * producers, and every one of them unreachable    take away
 * no producer at all                              keep
 * </pre>
 *
 * <p>The middle line is the only one that takes anything, and it is the one #479 is about. The first
 * covers everything unreadable — a call, a value bound elsewhere, a body that is a function — so a
 * helper that might answer anything keeps every case owed, which is the safe direction: a case left in
 * is a case the report asks for, and an author reading a gap they cannot fill has at least been told
 * something true about their model.
 *
 * <p>Only guards take an arm away, because only a guard's arm has a reachability proof behind it. A
 * {@code match} arm is left alone here: which cases of a sum can arrive is a different question, and
 * it is asked of the reading of the input ({@link PathReachability}).
 */
public final class ProducedCases {

    /**
     * The cases {@code body} can produce, which is the declared ones less those a guard's arm
     * proves unreachable.
     *
     * @param declared what the output type's cases are, which is what this answers where nothing is
     *                 taken away
     */
    public static Set<TypeSymbol> of(Core body, CoverageSites.Plan plan, PathReachability.Answers arrives,
                                   Set<TypeSymbol> declared) {
        // Nothing proven is nothing to take away: what this returns is `declared` less the cases whose
        // every producer is behind a proven arm, and with no such arm there are none. Skipped rather
        // than walked to the same answer.
        if (body == null || declared.isEmpty() || arrives.provesNothingUnreached()) {
            return declared;
        }
        Seen seen = new Seen();
        walk(body, List.of(), plan, arrives, declared, seen);
        if (seen.anythingUnreadable) {
            return declared;   // something reachable answers with what this cannot name
        }
        Set<TypeSymbol> out = new LinkedHashSet<>(declared);
        seen.behindAProvenArm.stream().filter(each -> !seen.reachable.contains(each)).toList()
                .forEach(out::remove);
        // The order the cases were declared in, which is the order they are named in. `Set.copyOf`
        // keeps the values and not the order, so a case taken out here would have reordered the ones
        // left — and what a report lists is read against the declaration it came from.
        return java.util.Collections.unmodifiableSet(out);
    }

    /** Where a case was answered with, which is what decides whether it can be answered at all. */
    private static final class Seen {

        /** Answered with somewhere no proof rules out. */
        private final Set<TypeSymbol> reachable = new LinkedHashSet<>();
        /** Answered with behind an arm nothing reaches, which is only worth acting on where the case
         * is answered with nowhere else. */
        private final Set<TypeSymbol> behindAProvenArm = new LinkedHashSet<>();
        /** A producer that could answer with anything, at a place something reaches. */
        private boolean anythingUnreadable;
    }

    /**
     * One tail position, and the arms it sits under.
     *
     * <p>Tail positions only. A construction evaluated on the way to somewhere else — an argument, the
     * value a {@code let} binds — is not what the behavior answers with, and counting it would keep a
     * case owed because the body happened to build one on its way past.
     */
    private static void walk(Core e, List<ArmProbe> under,
                             CoverageSites.Plan plan,
                             PathReachability.Answers arrives, Set<TypeSymbol> declared, Seen seen) {
        if (seen.anythingUnreadable) {
            return;   // nothing further can be taken away
        }
        switch (e) {
            case Core.Unreachable _ -> { }   // answers nothing, so it produces nothing
            case Core.LetIn li -> walk(li.body(), under, plan, arrives, declared, seen);
            case Core.If iff -> {
                ControlPointId.ArmOccurrence[] arms = plan.armsOf(iff);
                walk(iff.then(), beneath(under, arms, 0), plan, arrives, declared, seen);
                walk(iff.els(), beneath(under, arms, 1), plan, arrives, declared, seen);
            }
            case Core.Match m -> {
                ControlPointId.ArmOccurrence[] arms = plan.armsOf(m);
                for (int i = 0; i < m.cases().size(); i++) {
                    walk(m.cases().get(i).body(), beneath(under, arms, i), plan, arrives, declared,
                            seen);
                }
            }
            case Core.IfConstructed ic -> {
                ControlPointId.ArmOccurrence[] arms = plan.armsOf(ic);
                walk(ic.then(), beneath(under, arms, 0), plan, arrives, declared, seen);
                for (int i = 0; i < ic.els().size(); i++) {
                    walk(ic.els().get(i).body(), beneath(under, arms, i + 1), plan, arrives,
                            declared, seen);
                }
            }
            case Core.UnitValue u -> produce(u.data(), under, arrives, declared, seen);
            case Core.Construct nd -> produce(nd.typeName(), under, arrives, declared, seen);
            // Everything else answers something this cannot name: a call, a name read from a binding,
            // a function value. The top of the lattice, which keeps every case owed.
            case null, default -> produce(null, under, arrives, declared, seen);
        }
    }

    /** Where one producer puts the case it answers with. */
    private static void produce(TypeSymbol built, List<ArmProbe> under,
                                PathReachability.Answers arrives,
                                Set<TypeSymbol> declared, Seen seen) {
        boolean proven = under.stream().anyMatch(arrives::nothingArrivesAt);
        if (built == null || !declared.contains(built)) {
            // Not a case this can name. Reachable, it could be any of them and nothing is taken away;
            // behind a proven arm it answers nothing and says nothing about any case either.
            seen.anythingUnreadable |= !proven;
            return;
        }
        if (proven) {
            seen.behindAProvenArm.add(built);
        } else {
            seen.reachable.add(built);
        }
    }

    /** The arms of an inner fork, added to the ones already above it. An arm with no probe adds
     * nothing: there is no site for a proof to have been about. */
    private static List<ArmProbe> beneath(
            List<ArmProbe> under,
            ControlPointId.ArmOccurrence[] arms, int index) {
        if (arms == null || index >= arms.length || arms[index] == null
                || arms[index].probe().isEmpty()) {
            return under;
        }
        List<ArmProbe> out = new ArrayList<>(under);
        out.add(arms[index].probe().get());
        return List.copyOf(out);
    }

    private ProducedCases() {}
}
