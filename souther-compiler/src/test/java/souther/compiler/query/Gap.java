package souther.compiler.query;

/**
 * Somewhere a search for defects fell short, in the one vocabulary all of them use.
 *
 * <p>One word list and not one per searcher. A walk of two answers, a walk of one, and a count of
 * what this compiler can be asked all narrow what they look at, and each of them saying so in its
 * own way is the same fact written three times — which is how one of them came to say it and another
 * came to swallow it. Written once, a fourth searcher answers in words that already exist, and the
 * arms below are what a self-test is held to reaching.
 *
 * @param why what stopped it
 * @param at where, said the way whoever met it says places
 */
record Gap(Gap.Why why, String at) {

    /** Every way a search here can fall short of what it was asked to cover. */
    enum Why {
        /** A walk was cut short by its own bound before it reached the end. */
        BUDGET_EXHAUSTED,
        /** A field the runtime would not hand over, so what is under it went unasked. */
        A_FIELD_THAT_WOULD_NOT_OPEN,
        /** Something that holds itself. What is under it is covered where the walk first met it,
         *  and this is what keeps the holder from being judged on having found nothing. */
        A_GRAPH_THAT_LOOPS,
        /**
         * A container of one size whose members do not line up one to one by what they say.
         *
         * <p>Not a finding, because which of the two it is cannot be told from here: members that
         * hold a way of reading a store and members that name different things both arrive as
         * something with nothing to pair it with.
         */
        MEMBERS_THAT_DO_NOT_PAIR,
        /**
         * A collection whose equality is neither its order nor what it holds.
         *
         * <p>What pairs two containers is their own contract: a list is equal to another by
         * position, a set by membership. A collection that is neither answers to neither rule, and
         * pairing it by the order an iterator happens to give would compare a member with something
         * that is not its counterpart.
         */
        A_CONTAINER_WITH_NO_RULE_FOR_PAIRING,
        /** A class found where this compiler was compiled to and not loadable from here, so what it
         *  declares was never counted. */
        A_CLASS_THAT_WOULD_NOT_LOAD,
        /** A question one of two compilations of one input was put and the other was not, so the
         *  two have nothing to be compared over there. */
        A_QUESTION_ONLY_ONE_STORE_WAS_PUT,
        /**
         * Something denying its twin while a part of it denies too, and no way to tell whose denial
         * it is.
         *
         * <p>What settles that is where the thing's equality comes from, and for something that
         * wrote its own there is no way to read that off the class: an equality over the parts and
         * an equality over the address answer alike while a part is denying. Guessed at, the two
         * come out as one — which is how something whose equality is its address goes unnamed for as
         * long as anything under it also fails.
         */
        WHOSE_DENIAL_THIS_IS_CANNOT_BE_TOLD
    }

    @Override
    public String toString() {
        return why + " " + at;
    }
}
