/**
 * 2つのチームが共有するドメイン型。中身は {@code src/main/souther/money.sou} が宣言していて、
 * ここには Java の宣言は無い。
 *
 * <p>このファイルがあるのは、アノテーションプロセッサが javac の一部として動くからで、javac は
 * コンパイルする Java ソースが1つも無いと何もしない（"No sources to compile"）。.sou しか持たない
 * プロジェクトが1つも Java を書かずに済むようにするのは、まだできていない。
 */
package shared.money;
