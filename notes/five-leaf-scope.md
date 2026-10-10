# Complete mathematical scope: trees with exactly five leaves

This note accompanies the JSP problem recommendation prepared on 10 October 2026. It explains the combination of two cited results; it does not claim a new proof of the general Graceful Tree Conjecture or priority over earlier literature.

**Statement.** Every finite tree with exactly five leaves is graceful: if it has (q) edges, its vertices admit distinct labels in ({0,ldots,q}) whose absolute differences on the edges are exactly (1,ldots,q).

For a nontrivial finite tree, the degree-sum identity gives

\[
\#\{v:\deg(v)=1\}=2+\sum_{\deg(v)\geq3}(\deg(v)-2).
\]

With five leaves, the sum on the right is three. Its possible partitions are (3), (2+1), and (1+1+1). Thus the branch degrees are precisely one of (5), ((4,3)), or ((3,3,3)); every remaining vertex has degree at most two.

* In the one-branch case, the tree is a spider with five legs. Panpa, Imnang and Wasuanankul prove that these trees are graceful in **Theorem 3.4** of [*Graceful Labeling of Spider Graphs With at Most Five Legs*](https://doi.org/10.1155/jama/5826777), published 2 September 2025. Their Section 4 identifies the other two five-leaf branch patterns as directions for further work.
* In the other two cases, **Theorem 1.1** of [*Graceful Labelings of Five-Leaf Trees with Multiple Branch Vertices*](../papers/graceful-five-leaf-trees.pdf), by **Will Howe, Grant Huffman, Jensen Kohlmeyer and Liam Kruer**, states and proves gracefulness for every five-leaf tree with at least two branch vertices. Theorem 1.2 treats ((4,3)), and Theorem 8.1 treats ((3,3,3)).

These cases exhaust all finite trees with exactly five leaves, proving the stated fixed-leaf result. The earlier spider theorem is credited to its authors; it is not presented as new work by the four authors of the multiple-branch manuscript. The unrestricted Graceful Tree Conjecture remains outside this recommendation.

## Source and verification limits

The multiple-branch manuscript is internally dated 8 October 2026 and is reproduced without edits. Its appearance in this public source edition is on 10 October 2026; the internal date alone does not establish an earlier public disclosure. The manuscript discloses substantial OpenAI Codex assistance. This scope note was also prepared with Codex assistance.

The two archived Lean bodies, [Source10](../proofs/GracefulFiveLeafSource10.lean) and [Source11](../proofs/GracefulFiveLeafSource11.lean), concern the separate branch-pattern targets. They depend on the validator's problem declarations and environment. No fresh local compilation of these bodies, nor a complete Lean formalization of all three cases together, is asserted here. The recommendation supplies a complete mathematical argument and references; it is not a Lean registration or an award claim. JSP's mathematical review and catalog decision remain outstanding.
