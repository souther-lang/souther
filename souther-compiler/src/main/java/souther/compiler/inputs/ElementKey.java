package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

/**
 * What an element of a run is filed under: the way from the element to the value two elements are
 * one key by.
 *
 * <p>One way for every element ({@link At}), or one way for each case of a place of the element
 * ({@link ByCase}) — a fold whose element was made by a {@code match} that writes the key out of a
 * field of each case is filed under whichever of those fields the element's case has. Two elements
 * whose keys are equal are one key whichever arm each was read by.
 *
 * <p>No number: a key is compared for which values are equal and for nothing else, so a choice of
 * key is no {@link ElementValue.OfItsCase}, which is arithmetic over the arms.
 */
public sealed interface ElementKey {

    /** Every way from an element this reads to tell its key: the place whose case chooses among
     *  them, and the way each arm reads. */
    Set<ElementProjection> reads();

    /** Every way along which some element's key is read: the values found there are the keys. */
    List<ElementProjection> ways();

    /** The way {@code isOf}'s element is read along, the test being of its case where the key is
     *  chosen by one; or null where no arm takes the element. */
    ElementProjection readAlong(Predicate<CasesLeft> isOf);

    /** How a key is written, read from the elements at {@code elements}. */
    String spelledFrom(TermPath elements);

    /** How a key is written below an element: {@code itself} where it is the element. */
    String spelled();

    /**
     * Whether every element this reads a way for holds a value along it: a way of fields alone,
     * or one narrowing the subject to no fewer cases than its arm takes and going on by fields.
     * A narrowing anywhere else is of something an element of the arm's cases may not be.
     */
    boolean heldByEveryElementItTakes();

    /**
     * The key {@code arms} read, each arm taking the cases of the value at {@code subject} it
     * names: the one way they all read where they read one.
     */
    static ElementKey byCase(ElementProjection subject, List<ByCase.Arm> arms) {
        ElementProjection first = arms.getFirst().path();
        return arms.stream().allMatch(arm -> arm.path().equals(first)) ? new At(first)
                : new ByCase(subject, arms);
    }

    /** The one way every element is read along. */
    record At(ElementProjection path) implements ElementKey {

        public At {
            Objects.requireNonNull(path, "a key is read somewhere in the element");
        }

        @Override
        public Set<ElementProjection> reads() {
            return Set.of(path);
        }

        @Override
        public List<ElementProjection> ways() {
            return List.of(path);
        }

        @Override
        public ElementProjection readAlong(Predicate<CasesLeft> isOf) {
            return path;
        }

        @Override
        public String spelledFrom(TermPath elements) {
            return path.from(elements).discriminated();
        }

        @Override
        public String spelled() {
            return path.steps().isEmpty() ? "itself" : path.spelled();
        }

        @Override
        public boolean heldByEveryElementItTakes() {
            return path.fields() != null;
        }
    }

    /**
     * A key chosen by the case of the value at {@code subject}: an element is read along the way
     * of the arm taking its case, and along no other.
     *
     * <p>The arms take no case two of them take, so an element is read along one way at most; and
     * a way that narrows {@code subject} narrows it to cases its arm's are among, so it never asks
     * an element of one case for a field only another case has.
     */
    record ByCase(ElementProjection subject, List<Arm> arms) implements ElementKey {

        /** An arm: the cases of the subject it takes, and the way an element of them is read. */
        public record Arm(CasesLeft cases, ElementProjection path) {

            public Arm {
                Objects.requireNonNull(cases, "an arm takes some case");
                Objects.requireNonNull(path, "an arm reads its key somewhere");
            }
        }

        public ByCase {
            Objects.requireNonNull(subject, "a key chosen by case is chosen by a place's case");
            arms = List.copyOf(arms);
            if (arms.size() < 2) {
                throw new IllegalArgumentException("a key chosen by case chooses among ways");
            }
            for (int i = 0; i < arms.size(); i++) {
                Arm arm = arms.get(i);
                for (int j = i + 1; j < arms.size(); j++) {
                    if (arm.cases().meet(arms.get(j).cases()) != null) {
                        throw new IllegalArgumentException("two arms of a key take "
                                + arm.cases().meet(arms.get(j).cases()) + " of " + subject);
                    }
                }
                CasesLeft through = narrowingOf(subject, arm.path());
                if (through != null && !arm.cases().within(through)) {
                    throw new IllegalArgumentException("the arm taking " + arm.cases() + " of "
                            + subject + " reads " + arm.path() + ", which only some of them have");
                }
            }
        }

        /** What {@code path} narrows {@code subject} to on the way, or null where it goes through
         *  no narrowing of it. */
        private static CasesLeft narrowingOf(ElementProjection subject, ElementProjection path) {
            List<TermPath.Step> steps = path.steps();
            int at = subject.steps().size();
            return steps.size() > at && steps.subList(0, at).equals(subject.steps())
                    && steps.get(at) instanceof TermPath.Step.Refine(CasesLeft cases) ? cases
                    : null;
        }

        @Override
        public Set<ElementProjection> reads() {
            Set<ElementProjection> all = new LinkedHashSet<>();
            all.add(subject);
            arms.forEach(arm -> all.add(arm.path()));
            return Set.copyOf(all);
        }

        @Override
        public List<ElementProjection> ways() {
            return arms.stream().map(Arm::path).distinct().toList();
        }

        @Override
        public ElementProjection readAlong(Predicate<CasesLeft> isOf) {
            for (Arm arm : arms) {
                if (isOf.test(arm.cases())) {
                    return arm.path();
                }
            }
            return null;
        }

        @Override
        public String spelledFrom(TermPath elements) {
            List<String> said = new ArrayList<>();
            for (Arm arm : arms) {
                said.add("when " + subject.narrowedTo(arm.cases()).from(elements).discriminated()
                        + " then " + arm.path().from(elements).discriminated());
            }
            return String.join(" ", said);
        }

        @Override
        public String spelled() {
            List<String> said = new ArrayList<>();
            for (Arm arm : arms) {
                said.add("when " + subject.narrowedTo(arm.cases()).spelled() + " then "
                        + new At(arm.path()).spelled());
            }
            return String.join(" ", said);
        }

        @Override
        public boolean heldByEveryElementItTakes() {
            for (Arm arm : arms) {
                List<TermPath.Step> steps = arm.path().steps();
                int past = narrowingOf(subject, arm.path()) == null ? 0
                        : subject.steps().size() + 1;
                if (new ElementProjection(steps.subList(past, steps.size())).fields() == null) {
                    return false;
                }
            }
            return true;
        }
    }
}
