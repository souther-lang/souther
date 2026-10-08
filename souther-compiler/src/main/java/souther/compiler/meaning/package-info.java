/**
 * What a condition of the model means, read once and shared by every analysis that asks.
 *
 * <p>The subjects a condition is finally about — a position of the input, an answer a dependency
 * gave — and the quantities compared over them. Partitioning, coverage and reachability each do
 * their own work with a condition; what the condition states is decided here and nowhere else, so
 * two spellings of one statement cannot come out differently depending on which of them asked.
 *
 * <p>Read off the representation where the language's operations stand. The tree that runs is
 * where a run goes and what it records, and nothing here is read off it.
 */
package souther.compiler.meaning;
