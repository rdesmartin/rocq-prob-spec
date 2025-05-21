Title: Probabilistic Verification of Neuro-Symbolic Programs via ProbLog - Rocq Interface

Abstract: Neuro-symbolic programs are defined as programs that contain Machine learning (ML) models embedded into the symbolic code.
Verifying such programs is particularly hard: "neural" and "symbolic" components require very different methods of specification and verification of safety properties. 
In turn, this also means that they require a diversified programming language support, covering property-based training in languages such as Python,
verification of low-level constraints on ML models in linear programming (SMT Lib) style, and finally high-level system descriptions and proofs 
in the style of interactive theorem provers (ITP) such as Rocq, LEAN or Idris. The language Vehicle provides an interface that keeps all of these programing languages and components 
synchronised with respect to the ML model specification. Recently, we implemented a Vehicle backend to Rocq, with a view of enabling probabilistic reasoning about neuro-symbolic programs.  

Probabilistic reasoning naturally arises in all of the above mentioned aspects of Neuro-Symbolic specifications: 
- ML models are trained based on given data distributions;
- verification of ML models can be probabilistic; and finally,
- one may want to reason probabilstically about the properties of the symbolic programs that embed ML models.

In this talk, we will only consider the latter problem.
Concretely, the problem we consider can be expalined as follows:  
Given that certificates for a verified ML model can be passed over to the system specification written in an an ITP such as Rocq,
what sort of probabilistic reasoning about the neuro-symbolic program can be enbled on the Rocq side? 
As a tentative answer, we investigate a solution that deploys ProbLog and Rocq together.  
Problog is a probabilistic logic programming language, that we propose to use
for automating the discovery of probabilistic properties of neuro-symbolic programs.
We show that there is a generic procedure to lift Problog theorems to Rocq and then use Rocq's proability theory libraries 
to reconstruct the proofs and thus reason probabilsiically about the bigger system specification.   
