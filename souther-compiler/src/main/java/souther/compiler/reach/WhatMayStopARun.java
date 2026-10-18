package souther.compiler.reach;

/**
 * What worked out on the way to a place may stop a run on operands nothing here says.
 *
 * <p>Which kind of thing it is, and not where it is written. A reader told this is sent up the body
 * from the place to the first one of these, and the place itself is named beside it; a position
 * held here would be a place carried under a finding, which is what the module-boundary cut has to
 * wait on.
 *
 * <p>Made by the reading that walks the body, as every answer in this package is, and read by
 * everybody else: a kind is told apart by what it is, so an order over them is an order over the
 * kinds.
 */
public sealed interface WhatMayStopARun {

    /** What a sentence calls it. */
    String said();

    /** An operator answering on operands nothing here holds it to: a product of two values
     *  nothing bounds, a sum of decimals, a quotient by a value that may be nought. */
    record AnOperator() implements WhatMayStopARun {

        @Override
        public String said() {
            return "an operator";
        }
    }

    /** A call: a kernel that may stop, a behavior whose body is not this one, a function value. */
    record ACall() implements WhatMayStopARun {

        @Override
        public String said() {
            return "a call";
        }
    }

    /** A construction a rule of its type may refuse. */
    record AConstruction() implements WhatMayStopARun {

        @Override
        public String said() {
            return "a construction";
        }
    }
}
