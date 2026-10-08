package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

/**
 * What a condition states, about the subjects it is finally about.
 *
 * <p>Told apart by what it states and by nothing else: {@code p && q} and {@code q && p} are one
 * proposition, so are {@code p || p} and {@code p}, and so are every spelling of one comparison. A
 * conjunction or a disjunction is made through {@link #all} and {@link #any}, which put their parts in
 * one order and keep each once. Which construct each part was read from, and in what order a run
 * meets them, are not here: the first is {@link WhatAConditionSays}'s and the second the run's.
 *
 * <p>Denial is pushed down to the parts ({@link #denied}), so there is no arm for it: what a part
 * holds or fails is the {@code holds} it carries, and a quantifier denied is the other quantifier.
 */
public sealed interface Proposition {

    /** What holds exactly where this does not. */
    Proposition denied();

    /** A spelling that tells two propositions apart exactly where they are two, and orders parts. */
    String key();

    /** Comes out {@code holds} for every row. */
    record Always(boolean holds) implements Proposition {

        @Override
        public Proposition denied() {
            return new Always(!holds);
        }

        @Override
        public String key() {
            return String.valueOf(holds);
        }
    }

    /** A relation over quantities, held or failing. */
    record Compared(Relation relation, boolean holds) implements Proposition {

        public Compared {
            if (relation == null) {
                throw new IllegalArgumentException("a comparison states some relation");
            }
        }

        @Override
        public Proposition denied() {
            return new Compared(relation, !holds);
        }

        @Override
        public String key() {
            return (holds ? "" : "!") + relation;
        }
    }

    /** A subject read for its truth, holding or failing. */
    record Truth(DecisionSubject of, boolean holds) implements Proposition {

        public Truth {
            if (of == null) {
                throw new IllegalArgumentException("a truth is a truth of something");
            }
        }

        @Override
        public Proposition denied() {
            return new Truth(of, !holds);
        }

        @Override
        public String key() {
            return (holds ? "" : "!") + of.spelled();
        }
    }

    /**
     * A subject being one of {@code cases}, or not.
     *
     * <p>The cases selected and not the fork that selected them: a match of three arms is three
     * propositions about one subject, one per arm.
     */
    record InCases(DecisionSubject of, CasesLeft cases, boolean holds) implements Proposition {

        public InCases {
            if (of == null || cases == null) {
                throw new IllegalArgumentException("a case is some subject's, and some cases");
            }
        }

        @Override
        public Proposition denied() {
            return new InCases(of, cases, !holds);
        }

        @Override
        public String key() {
            return (holds ? "" : "!") + of.spelled() + " is " + cases.spelled();
        }
    }

    /** An optional subject holding a value, or not. */
    record Present(DecisionSubject of, boolean holds) implements Proposition {

        public Present {
            if (of == null) {
                throw new IllegalArgumentException("a value is present at some subject");
            }
        }

        @Override
        public Proposition denied() {
            return new Present(of, !holds);
        }

        @Override
        public String key() {
            return (holds ? "" : "!") + "present " + of.spelled();
        }
    }

    /**
     * Two subjects holding the same value, or not — what a container holding a value asks of one
     * of its elements.
     */
    record SameValue(DecisionSubject one, DecisionSubject other, boolean holds)
            implements Proposition {

        public SameValue {
            if (one == null || other == null) {
                throw new IllegalArgumentException("a sameness is of two subjects");
            }
        }

        @Override
        public Proposition denied() {
            return new SameValue(one, other, !holds);
        }

        @Override
        public String key() {
            return one.spelled() + (holds ? " == " : " /= ") + other.spelled();
        }
    }

    /** Every part holding. Made through {@link #all}. */
    record All(List<Proposition> parts) implements Proposition {

        public All {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a conjunction is of two or more parts");
            }
        }

        @Override
        public Proposition denied() {
            return any(parts.stream().map(Proposition::denied).toList());
        }

        @Override
        public String key() {
            return "all" + parts.stream().map(Proposition::key).toList();
        }
    }

    /** Some part holding. Made through {@link #any}. */
    record Any(List<Proposition> parts) implements Proposition {

        public Any {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a disjunction is of two or more parts");
            }
        }

        @Override
        public Proposition denied() {
            return all(parts.stream().map(Proposition::denied).toList());
        }

        @Override
        public String key() {
            return "any" + parts.stream().map(Proposition::key).toList();
        }
    }

    /**
     * Some element of the container at {@code container} meeting {@code ofTheElement} — or, where
     * {@code holds} is false, no element meeting it.
     *
     * <p>The element is what stands at {@code container}'s element inside {@code ofTheElement}: a
     * subject under {@code container[*]} there is the element's — and of a map, whose element is an
     * entry, so is one under {@code container[key]} — and nothing else is. Which is why
     * the same container is never quantified twice inside one proposition: the two elements would be
     * one subject, and the proposition would say {@code x < x} where it was asked about two of them.
     */
    record Some(TermPath container, Proposition ofTheElement, boolean holds)
            implements Proposition {

        public Some {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a quantifier is over some container");
            }
        }

        @Override
        public Proposition denied() {
            return new Some(container, ofTheElement, !holds);
        }

        @Override
        public String key() {
            return (holds ? "some " : "no ") + container + " [" + ofTheElement.key() + "]";
        }
    }

    /**
     * Part of a condition nothing read the meaning of, told apart by where the reading stopped.
     *
     * <p>The one proposition told apart by a name. Two parts nothing could read mean nothing to be
     * told apart by, so without one they would be one part, and a condition stating two things
     * nobody read would read as stating one.
     *
     * @param where   the construct of the model the condition is, where the reader knows it — a
     *                reader asking only which answers a condition can give has no construct to name
     *                and needs none, since it never compares two unread parts
     * @param ordinal which unread part of the condition this is, in the order the reading met them
     * @param why     what stopped it, in the stopping reader's words
     * @param fixed   whether it is the same whatever the input, which is all that is known of it
     */
    record Unread(Optional<ModelOccurrence> where, int ordinal, WhyUnread why, boolean fixed,
                  boolean holds) implements Proposition {

        public Unread {
            if (where == null || why == null) {
                throw new IllegalArgumentException("an unread part stopped somewhere, for a reason");
            }
        }

        @Override
        public Proposition denied() {
            return new Unread(where, ordinal, why, fixed, !holds);
        }

        @Override
        public String key() {
            return (holds ? "" : "!") + "unread " + where.map(String::valueOf).orElse("")
                    + "#" + ordinal;
        }
    }

    /**
     * Every one of {@code parts} holding: what holds of all of them, with a part that always holds
     * left out, one that never does settling it, and each part kept once in one order.
     */
    static Proposition all(List<Proposition> parts) {
        return joined(parts, true);
    }

    /** Some one of {@code parts} holding, the same way round. */
    static Proposition any(List<Proposition> parts) {
        return joined(parts, false);
    }

    private static Proposition joined(List<Proposition> parts, boolean every) {
        Set<String> seen = new LinkedHashSet<>();
        List<Proposition> kept = new ArrayList<>();
        for (Proposition part : parts) {
            List<Proposition> flat = switch (part) {
                case All all when every -> all.parts();
                case Any any when !every -> any.parts();
                default -> List.of(part);
            };
            for (Proposition one : flat) {
                if (one instanceof Always(boolean holds)) {
                    if (holds != every) {
                        return one;
                    }
                    continue;
                }
                if (seen.add(one.key())) {
                    kept.add(one);
                }
            }
        }
        kept.sort(Comparator.comparing(Proposition::key));
        return switch (kept.size()) {
            case 0 -> new Always(every);
            case 1 -> kept.getFirst();
            default -> every ? new All(kept) : new Any(kept);
        };
    }
}
