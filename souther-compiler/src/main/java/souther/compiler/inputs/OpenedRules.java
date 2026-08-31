package souther.compiler.inputs;

/**
 * One value's rules, and the condition the reading of them holds under.
 *
 * <p>The two together because a reader of the first needs the second to know what it may do with it.
 * What a case's clauses say is true of the rows whose value turned out to be that case, and a
 * reading handed the rules alone can only take them for rules about every row — which is a sum's
 * cases meeting into one space and refusing an input between them.
 *
 * @param rules   what the declaration at this root states
 * @param opening why the reading was opened here, which says when what it states holds
 */
record OpenedRules(PlacedRules rules, RootOpening opening) {}
