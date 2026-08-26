/**
 * What a behavior is measured at, and what measuring it is allowed to spend.
 *
 * <p>The positions a model divides are read here ({@link souther.compiler.partition.Partitions}),
 * what each measure's reading came to is settled beside them
 * ({@link souther.compiler.partition.MeasureClosure}), and rows for what the reading left uncovered
 * are composed from them ({@link souther.compiler.partition.Generator}).
 *
 * <h2>Where a resource limit may go</h2>
 *
 * <p>Several things here are bounded, because their cost is decided by the source: the pair space a
 * behavior's positions span, the rows one call writes, the cells one group of the body's decisions
 * expands to. Four rules govern all of them, decided in ADR-0113. They are stated here rather than
 * beside any one limit, because what they are about is where a limit may be put at all.
 *
 * <p><b>This is what the subsystem is held to.</b> Axis discovery conforms since #969, and the
 * three limits above conform since #1005: each is held where its own cost is incurred, each says
 * what exhausting it left undone, and all three are read off {@link
 * souther.compiler.partition.AdequacyPolicy}, which the compilation sets and hands to the analysis.
 *
 * <p><b>1. Semantic evidence is never pre-selected by a resource budget.</b> Every semantic subject
 * the reading reaches is offered to the readers that measure it. A reading may still fail to derive
 * or understand one; what it may not do is select the subject away to save work.
 *
 * <p>The distinction is the whole of the rule and is easy to lose. Readings here do stop — a walk
 * goes two levels into a value and no further, {@link souther.compiler.check.ReadingPolicy} will not
 * hold a wide clause's alternatives apart, a rule may be one this compiler cannot turn into a line.
 * None of those is a budget choosing which evidence to keep: the position is still there, and what
 * the reading could not do with it is reported at that position — {@code notRead},
 * {@link souther.compiler.partition.ReadingResidue}, {@code PositionValuesNotSeparated}. A
 * limit that takes the position out of the measure is different in kind, because a position nobody
 * measured leaves the same absence as one the rows cover.
 *
 * <p><b>2. Budgets guard expensive operations, not semantic inputs.</b> A limit belongs at the
 * operation whose cost it bounds, and after the semantic inputs to that operation are known. Pair
 * enumeration, row generation and cell expansion are such operations. The number of positions a
 * behavior takes is not one — it is an input to those operations, and by rule 1 not a place to
 * spend a budget.
 *
 * <p><b>3. Every budget exhaustion is observable.</b> A compiler-imposed loss of evidence is
 * represented in the result at the point where the loss occurs, and reaches every projection of that
 * result unchanged — the human report, the JSON document, an API. A limit that fires and hands back
 * a value saying nothing is worse than the loss it caused: a measure that was weakened then reads
 * exactly like one that found nothing to say.
 *
 * <p><b>4. Resource policy belongs to the compilation.</b> A limit is an input the query graph hands
 * to the analysis, the way {@link souther.compiler.check.ReadingPolicy} and
 * {@link souther.compiler.examples.EvaluationPolicy} already are, rather than a private constant or
 * a system property read wherever the work happens. {@link
 * souther.compiler.partition.AdequacyPolicy} is where the three are written, grouped by which
 * result each weakens — a caller raising one to lift a partial measurement should not as readily
 * raise one that cannot change it.
 *
 * <h2>What these were written from</h2>
 *
 * <p>A limit on how many axes one behavior is measured at, which was 12 (issue #969). Measured, it
 * protected neither of the two things a limit here could protect: a dropped axis printed a line of
 * its own, one for one with the line a measured axis prints, so no report was shorter for it; and
 * the measure is close to linear in the count, while what the pairs and the rows cost was bounded
 * at the pair space and at the row budget already. Removing it cost milliseconds on models of a
 * hundred positions, and on models where the row budget binds first it was faster without.
 *
 * <p>It did not bound what it named, either. The budget was spent before the body was read and only
 * on axes measurable by then, so a plain {@code Int} passed free and became a boundary axis
 * afterwards: twelve {@code Flag} fields beside five plain {@code Int}s a body compares reported
 * seventeen axes under a limit of twelve.
 *
 * <p>Which is rules 1 and 2 rather than a detail of one constant. The drop happened at the one point
 * in the pipeline where the least is known about what is being dropped — an axis dropped in
 * {@code Partitions.of} never reaches {@code withThresholds}, so what a {@code guard} would have
 * drawn on it was never knowable. What went with the limit is everything that accounted for it: the
 * dropped axis and what it was carrying, the closure gap filing it under the measure it cost, the
 * finding, the report's line and the JSON's array. That machinery satisfied rule 3 and was a
 * faithful account of a loss that need not have happened.
 */
package souther.compiler.partition;
