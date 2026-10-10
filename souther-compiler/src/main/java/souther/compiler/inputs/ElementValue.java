package souther.compiler.inputs;

import souther.compiler.check.AffineForms;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * What a closure computed from one element of a walk, for a closure whose answer is not a place of
 * the element.
 *
 * <p>The number a walk answers per element when that number is made from the element's fields: an
 * affine form of them, or the choice between two such numbers by a flag the element holds. Relative
 * to the element, so it can be joined to whichever position the run is over, as an
 * {@link ElementProjection} is — and the atoms of a form are those projections, so a field of the
 * element is named the one way wherever it is read.
 *
 * <p><b>The arithmetic is {@link AffineForms}'s.</b> The grammar of what composes a form is the
 * language's, written once; this supplies only what an atom of an element is called. What this
 * adds is the choice, which no form holds: a branch on a flag is one form where the flag is set and
 * another where it is not, and a single form over the element's fields would have to say which.
 *
 * <p>Not a place. {@link ElementProjection} is where in an element a value stands, and a computed
 * number stands nowhere in it. Held apart so a rule about what a walk computed is never read as a
 * rule about a field.
 *
 * <p>Only what is read exactly. A product of two fields, a call the library does not say the form
 * of, a branch on anything but a flag the element holds: none is read, and the walk is a run this
 * compiler did not read rather than one it read wrongly.
 */
public sealed interface ElementValue {

    /** The fields of the element this reads, in no order a reader may rely on. */
    Set<ElementProjection> reads();

    /**
     * What this comes to for one element, given the number each field of it holds and which flags
     * are set; or null where a field it reads is one the element has no number or flag at.
     */
    ExactRatio at(Function<ElementProjection, ExactRatio> numberAt,
                  Function<ElementProjection, Boolean> flagAt);

    /** {@code const + Σ coef·field}. */
    record Affine(LinearForm<ElementProjection> form) implements ElementValue {

        public Affine {
            if (form == null) {
                throw new IllegalArgumentException("a number made of the element is a form of it");
            }
        }

        @Override
        public Set<ElementProjection> reads() {
            return Set.copyOf(form.coefs().keySet());
        }

        @Override
        public ExactRatio at(Function<ElementProjection, ExactRatio> numberAt,
                             Function<ElementProjection, Boolean> flagAt) {
            ExactRatio total = form.constant();
            for (Map.Entry<ElementProjection, ExactRatio> each : form.coefs().entrySet()) {
                ExactRatio held = numberAt.apply(each.getKey());
                if (held == null) {
                    return null;
                }
                ExactRatio weighed = each.getValue().times(held).orNull();
                total = weighed == null ? null : total.plus(weighed).orNull();
                if (total == null) {
                    return null;
                }
            }
            return total;
        }

        @Override
        public String toString() {
            List<String> terms = new ArrayList<>();
            form.coefs().entrySet().stream()
                    .sorted(Map.Entry.comparingByKey(
                            java.util.Comparator.comparing(ElementProjection::toString)))
                    .forEach(each -> terms.add(each.getValue() + "·" + each.getKey()));
            terms.add(form.constant().toString());
            return String.join(" + ", terms);
        }
    }

    /** {@code whenSet} where the element's flag {@code flag} is set, and {@code otherwise} where it
     *  is not. */
    record Choose(ElementProjection flag, ElementValue whenSet, ElementValue otherwise)
            implements ElementValue {

        public Choose {
            if (flag == null || whenSet == null || otherwise == null) {
                throw new IllegalArgumentException("a choice is of a flag and both of its answers");
            }
        }

        @Override
        public Set<ElementProjection> reads() {
            Set<ElementProjection> all = new LinkedHashSet<>();
            all.add(flag);
            all.addAll(whenSet.reads());
            all.addAll(otherwise.reads());
            return Set.copyOf(all);
        }

        @Override
        public ExactRatio at(Function<ElementProjection, ExactRatio> numberAt,
                             Function<ElementProjection, Boolean> flagAt) {
            Boolean set = flagAt.apply(flag);
            return set == null ? null
                    : (set ? whenSet : otherwise).at(numberAt, flagAt);
        }

        @Override
        public String toString() {
            return "if " + flag + " then " + whenSet + " else " + otherwise;
        }
    }

    /**
     * What a licensed closure computed of its element, or null where that is not read.
     *
     * <p>Asked after {@link ElementProjection#read} has answered null: an answer that is a place of
     * the element is a place and is not made into a one-field form. Wherever the closure's answer is
     * arithmetic over fields, a name bound to either, or a branch on a flag between two of them, this
     * says which.
     *
     * @param held what each binding of the body holds, so that a name on the way is read through
     */
    static ElementValue read(ElementAnswer answer, Map<BindingId, Core> held,
                             RuleReadingSource source) {
        return new Reader(answer.parameter(), held, source).value(answer.body(), new HashSet<>());
    }

    /** One reading of one closure's answer. */
    final class Reader {

        private final BindingId element;
        private final Map<BindingId, Core> held;
        private final RuleReadingSource source;

        private Reader(BindingId element, Map<BindingId, Core> held, RuleReadingSource source) {
            this.element = element;
            this.held = held;
            this.source = source;
        }

        private ElementValue value(Core answer, Set<BindingId> met) {
            Core e = Core.withoutStanding(answer);
            if (e instanceof Core.LetIn let) {
                return value(let.body(), met);
            }
            // A name given a branch is the branch, and a name given arithmetic is read by the
            // arithmetic's own walk below.
            if (e instanceof Core.Read read && !element.equals(read.binding())
                    && held.get(read.binding()) != null
                    && Core.withoutStanding(held.get(read.binding())) instanceof Core.If) {
                return met.add(read.binding()) ? value(held.get(read.binding()), met) : null;
            }
            if (e instanceof Core.If branch) {
                ElementProjection flag =
                        ElementProjection.read(branch.cond(), element, held, source.newtypes());
                ElementValue yes = flag == null ? null : value(branch.then(), met);
                ElementValue no = yes == null ? null : value(branch.els(), met);
                return no == null ? null : new Choose(flag, yes, no);
            }
            LinearForm<ElementProjection> form = AffineForms.of(e, held, atoms());
            return form == null ? null : new Affine(form);
        }

        /** What an atom of an element is called: the way to it from the element, and what a name on
         *  the way holds. */
        private AffineForms.Reading<ElementProjection, Map<BindingId, Core>> atoms() {
            return new AffineForms.Reading<>() {

                @Override
                public Symbols symbols() {
                    return source.symbols();
                }

                @Override
                public DeclarationAccess declarations() {
                    return source.declarations();
                }

                @Override
                public LinearForm<ElementProjection> leafOf(Core e, Map<BindingId, Core> at) {
                    ElementProjection place =
                            ElementProjection.read(e, element, at, source.newtypes());
                    return place == null ? null : LinearForm.atom(place);
                }

                @Override
                public Map<BindingId, Core> inside(Core.LetIn li, Map<BindingId, Core> at) {
                    return at;
                }

                @Override
                public AffineForms.ReadThrough<Map<BindingId, Core>> readThrough(
                        Core.Read read, Map<BindingId, Core> at) {
                    Core value = element.equals(read.binding()) ? null : at.get(read.binding());
                    return value == null ? null : new AffineForms.ReadThrough<>(value, at);
                }

                @Override
                public List<AffineForms.ReadThrough<Map<BindingId, Core>>> alternativesOf(
                        Core.Read read, Map<BindingId, Core> at) {
                    return null;
                }

                @Override
                public boolean readsThrough(Core.FieldAccess fa, Map<BindingId, Core> at) {
                    return false;
                }
            };
        }
    }
}
