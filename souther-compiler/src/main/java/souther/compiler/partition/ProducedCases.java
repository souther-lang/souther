package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The cases of its output a body may answer with.
 *
 * <p>Asked because a case is owed a row only where something can produce it. An arm nothing reaches
 * produces nothing, and a case produced nowhere else is then a case the signature would ask for and
 * no row could give — the same obligation the classes and the lines have already stopped asking for.
 *
 * <p>A may-analysis, so the answer is only ever too wide. What one producer contributes is
 *
 * <pre>
 * nothing               where an arm it sits under is proven unreachable
 * the case it builds    where the value it builds names one
 * every declared case   otherwise
 * </pre>
 *
 * and the answer is their union. The last line is the top of the lattice and it is where everything
 * this cannot read goes: a call, a value bound elsewhere, a body that is a function. So a helper that
 * might answer anything keeps every case owed, which is the safe direction — a case left in is a case
 * the report asks for, and an author reading a gap they cannot fill has at least been told something
 * true about their model.
 *
 * <p>Only guards take an arm away, because only a guard's arm has a reachability proof behind it. A
 * {@code match} arm is left alone: which cases of a sum can arrive is a different question and
 * {@link Exclusions} is where it is asked.
 */
public final class ProducedCases {

    /**
     * <p>Asked of every body, and not only of one with an arm this can rule out. What a body may
     * answer with is a fact about the body: reading it only where a guard happens to be provable
     * would make the same two bodies answer differently, and adding a guard nothing reaches to a
     * behavior would change what its signature is owed.
     *
     * @param declared what the output type's cases are, which is both the answer where nothing can be
     *                 read and the set every unresolved producer contributes
     */
    public static Set<TypeName> of(Core body, CoverageSites.Plan plan, GuardReachability reachable,
                                   Set<TypeName> declared) {
        if (body == null || declared.isEmpty()) {
            return declared;   // nothing to read, so every case the type has stays owed
        }
        Set<TypeName> found = new LinkedHashSet<>();
        walk(body, List.of(), plan, reachable, declared, found);
        return found;
    }

    /**
     * One tail position, and the arms it sits under.
     *
     * <p>Tail positions only. A construction evaluated on the way to somewhere else — an argument, the
     * value a {@code let} binds — is not what the behavior answers with, and counting it would keep a
     * case owed because the body happened to build one on its way past.
     */
    private static void walk(Core e, List<Integer> under, CoverageSites.Plan plan,
                             GuardReachability reachable, Set<TypeName> declared,
                             Set<TypeName> found) {
        if (found.size() == declared.size()) {
            return;   // already the whole set; nothing further can widen it
        }
        switch (e) {
            case Core.Unreachable _ -> { }   // answers nothing, so it produces nothing
            case Core.LetIn li -> walk(li.body(), under, plan, reachable, declared, found);
            case Core.If iff -> {
                int[] arms = plan.probesOf(iff);
                walk(iff.then(), beneath(under, arms, 0), plan, reachable, declared, found);
                walk(iff.els(), beneath(under, arms, 1), plan, reachable, declared, found);
            }
            case Core.Match m -> {
                int[] arms = plan.probesOf(m);
                for (int i = 0; i < m.cases().size(); i++) {
                    walk(m.cases().get(i).body(), beneath(under, arms, i), plan, reachable, declared,
                            found);
                }
            }
            case Core.IfConstructed ic -> {
                int[] arms = plan.probesOf(ic);
                walk(ic.then(), beneath(under, arms, 0), plan, reachable, declared, found);
                for (int i = 0; i < ic.els().size(); i++) {
                    walk(ic.els().get(i).body(), beneath(under, arms, i + 1), plan, reachable,
                            declared, found);
                }
            }
            case Core.UnitValue u -> produce(u.data(), under, reachable, declared, found);
            case Core.NewData nd -> produce(nd.typeName(), under, reachable, declared, found);
            // Everything else answers something this cannot name: a call, a name read from a binding,
            // a function value. The top of the lattice, which keeps every case owed.
            case null, default -> produce(null, under, reachable, declared, found);
        }
    }

    /** What one producer contributes, which is nothing at all where an arm above it is unreachable. */
    private static void produce(TypeName built, List<Integer> under, GuardReachability reachable,
                                Set<TypeName> declared, Set<TypeName> found) {
        for (int site : under) {
            if (reachable.provenUnreachable(site)) {
                return;
            }
        }
        if (built != null && declared.contains(built)) {
            found.add(built);
            return;
        }
        found.addAll(declared);
    }

    /** The arms of an inner fork, added to the ones already above it. An arm with no probe adds
     * nothing: there is no site for a proof to have been about. */
    private static List<Integer> beneath(List<Integer> under, int[] arms, int index) {
        if (arms == null || index >= arms.length || arms[index] == CoverageSites.NO_SITE) {
            return under;
        }
        List<Integer> out = new ArrayList<>(under);
        out.add(arms[index]);
        return List.copyOf(out);
    }

    private ProducedCases() {}
}
