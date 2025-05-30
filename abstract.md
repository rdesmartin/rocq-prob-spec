Title: Probabilistic Verification of Neuro-Symbolic Programs via ProbLog - Rocq Interface

Ekaterina Komendantskaya, Jairo Marulanda-Giraldo, Remi Desmartin

Abstract: Neuro-symbolic programs are defined as programs that contain Machine learning (ML) models embedded into the symbolic code. Verifying such programs is particularly hard: "neural" and "symbolic" components require very different methods of specification and verification of safety properties. In turn, this also means that they require a diversified programming language support, covering property-based training in languages such as Python, verification of low-level constraints on ML models in linear programming (SMT Lib) style, and finally high-level system descriptions and proofs in the style of interactive theorem provers (ITP) such as Agda, Rocq, LEAN or Idris. The language Vehicle provides an interface that keeps all of these programming languages and components synchronised with respect to the ML model specification. Recently, we implemented a Vehicle backend to Rocq, with a view of enabling probabilistic reasoning about neuro-symbolic programs in Rocq's Mathematical Components libraries.

Probabilistic reasoning naturally arises in all of the above mentioned aspects of Neuro-Symbolic specifications:
-- ML models are trained based on given data distributions;
-- verification of ML models can be probabilistic; and finally,
-- one may want to reason probabilstically about the properties of the symbolic programs that embed ML models.

In this talk, we will only consider the latter problem. Concretely, the problem we consider can be explained as follows:
Given that certificates for a verified ML model can be passed over to the system specification written in an an ITP such as Rocq, what sort of probabilistic reasoning about the neuro-symbolic program can be enabled on the Rocq side? As a tentative answer, we investigate a solution that deploys ProbLog and Rocq together. Problog is a probabilistic logic programming language, that we propose to use for automating the discovery of probabilistic properties of neuro-symbolic programs. We show that there is a generic procedure to lift Problog theorems to Rocq and then use Rocq's probability theory libraries to reconstruct the proofs and thus reason probabilistically about the bigger system specification.

References:
1. Matthew L. Daggitt, Wen Kokke, Robert Atkey, Ekaterina Komendantskaya, Natalia Slusarz and Luca Arnaboldi. Vehicle: Bridging the Embedding Gap in the Verification of Neuro-Symbolic Programs. Invited paper at 10th International Conference on Formal Structures for Computation and Deduction (FSCD'25).
2. E. Komendantskaya. Proof-Carrying Neuro-Symbolic Code. Invited Paper at Computability in Europe, CiE'25.
3. L. Cordeiro, M. Daggitt, J. Girard-Satabin, O. Isac, T. Johnson, G. Katz, E. Komendantskaya, A. Lemesle, E. Manino, A. Sinkarovs, and H. Wu. Neural Network Verification is a Programming Lan- guage Challenge. European Symposium on Programming (ESOP 2025).
