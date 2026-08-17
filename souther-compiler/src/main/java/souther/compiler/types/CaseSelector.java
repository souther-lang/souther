package souther.compiler.types;

/**
 * One case a subject can be selected as: the name it is written by, and what the value turns out to
 * be once it has been ({@link Refinement}).
 *
 * <p>A <em>selector</em> rather than a variant or a partition, because one value can satisfy more
 * than one of them. A data may be a case of two named sums declared in its module, and the classes
 * generated for it implement the interface of each, so testing two selectors of one subject can both
 * answer yes. What that means is the reader's to decide — a {@code match} takes the first arm whose
 * selector answers, a behavior's declared relation holds every rule whose selector answers — and
 * nothing here decides it for them.
 *
 * <p>The name and the carrier agree, and are made together so that they cannot disagree. An
 * optional's carriers are named by the optional's own cases and nothing else may be: a selector
 * spelled {@code Some} whose carrier were the absent one would be tested as absent and reported as
 * present, and a reader would have no way to tell which half was the mistake.
 */
public record CaseSelector(TypeSymbol name, Refinement refinement) {

    public CaseSelector {
        if (name == null || refinement == null) {
            throw new IllegalArgumentException("a selector is a name and what it refines the value to");
        }
        if (named(refinement) != null && !named(refinement).equals(name)) {
            throw new IllegalArgumentException(
                    "an optional's carrier is named by the case it is: " + name + " is not "
                            + named(refinement));
        }
        if (named(refinement) == null && (TypeSymbol.SOME.equals(name) || TypeSymbol.NONE.equals(name))) {
            throw new IllegalArgumentException("an optional's case is one of its own carriers: " + name);
        }
    }

    /** A case whose carrier is the value: a union member, or a case of a named sum. */
    public static CaseSelector direct(TypeSymbol name, Type bound) {
        return new CaseSelector(name, new Refinement.Direct(bound));
    }

    /** The carrier an optional holding {@code element} is. */
    public static CaseSelector optionPresent(Type element) {
        return new CaseSelector(TypeSymbol.SOME, new Refinement.OptionPresent(element));
    }

    /** The carrier an optional holding nothing is. */
    public static CaseSelector optionAbsent() {
        return new CaseSelector(TypeSymbol.NONE, new Refinement.OptionAbsent());
    }

    /** What a value selected by this is read as, or null where nothing readable stands under it. */
    public Type bound() {
        return refinement.bound();
    }

    /** The case a carrier is the one of, for the carriers that are a particular case; null for one
     *  that stands for whatever case names it. */
    private static TypeSymbol named(Refinement refinement) {
        return switch (refinement) {
            case Refinement.Direct ignored -> null;
            case Refinement.OptionPresent ignored -> TypeSymbol.SOME;
            case Refinement.OptionAbsent ignored -> TypeSymbol.NONE;
        };
    }
}
