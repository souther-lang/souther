package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * Which conditions about names the cases of a sum share choose their cases together.
 *
 * <p>A condition under the cases is one requirement per case it can be under, and each of those
 * holds two things: what the row already was to get there — the cases of the sums above the name,
 * the same under every case — and the case the condition chooses. Only the second is a choice. Two
 * conditions under one outer case and about two sums inside it each choose a case of their own sum,
 * and reading the outer case they both stand under as something they choose together would ask for
 * every combination of the two choices where the cases of each are all there is.
 *
 * <p>So two conditions go together where one of them chooses at a sum the other speaks of, or where
 * what both take as given about one sum differs and has to be met. Where they take one sum as given
 * and alike, nothing about either choice touches the other.
 */
final class CaseChoices {

    private CaseChoices() {}

    /**
     * The conditions {@code underEach} describes, in groups whose cases are chosen together, each
     * group as indices in the order the conditions are given.
     *
     * @param underEach for each condition, what a row is taken to be under each case it can be under
     */
    static List<List<Integer>> chosenTogether(List<List<Requirements>> underEach) {
        List<Choice> choices = new ArrayList<>();
        for (List<Requirements> one : underEach) {
            choices.add(Choice.of(one));
        }
        int[] group = new int[choices.size()];
        for (int i = 0; i < group.length; i++) {
            group[i] = i;
        }
        for (int i = 0; i < group.length; i++) {
            for (int j = 0; j < i; j++) {
                if (choices.get(i).meets(choices.get(j))) {
                    int from = group[i];
                    int to = group[j];
                    for (int k = 0; k < group.length; k++) {
                        if (group[k] == from) {
                            group[k] = to;
                        }
                    }
                }
            }
        }
        Map<Integer, List<Integer>> out = new LinkedHashMap<>();
        for (int i = 0; i < group.length; i++) {
            out.computeIfAbsent(group[i], _ -> new ArrayList<>()).add(i);
        }
        return List.copyOf(out.values());
    }

    /**
     * What one condition takes as given and what it chooses.
     *
     * @param given  the sums every case of it requires alike, with what they require there
     * @param chosen the sums its cases require differently, or only some of them require anything of
     */
    private record Choice(Map<TermPath, CasesLeft> given, Set<TermPath> chosen) {

        static Choice of(List<Requirements> underEach) {
            Set<TermPath> spoken = new LinkedHashSet<>();
            for (Requirements each : underEach) {
                spoken.addAll(each.refinements().keySet());
            }
            Map<TermPath, CasesLeft> given = new LinkedHashMap<>();
            Set<TermPath> chosen = new LinkedHashSet<>();
            for (TermPath sum : spoken) {
                CasesLeft first = underEach.getFirst().at(sum);
                boolean alike = first != null;
                for (Requirements each : underEach) {
                    alike &= Objects.equals(first, each.at(sum));
                }
                if (alike) {
                    given.put(sum, first);
                } else {
                    chosen.add(sum);
                }
            }
            return new Choice(given, chosen);
        }

        /** Whether this and {@code other} choose their cases together. */
        boolean meets(Choice other) {
            for (TermPath sum : chosen) {
                if (other.speaksOf(sum)) {
                    return true;
                }
            }
            for (TermPath sum : other.chosen) {
                if (speaksOf(sum)) {
                    return true;
                }
            }
            for (Map.Entry<TermPath, CasesLeft> each : given.entrySet()) {
                CasesLeft theirs = other.given.get(each.getKey());
                if (theirs != null && !theirs.equals(each.getValue())) {
                    return true;
                }
            }
            return false;
        }

        private boolean speaksOf(TermPath sum) {
            return given.containsKey(sum) || chosen.contains(sum);
        }
    }
}
