# Higher-Order Ontological Arguments

## Introduction
project work for the computational metaphysics course of christoph benzmueller 2016

please use the following keywords for formalizations:

* entails
* closed
* godessential
* godlike

## Structure of Sourcecode
The sourcecode is divided into 3 components: *definitions*, *theorems* and *tests*.
All used definitions and abbreviations a stored inside the definitions subfolder. All theorem files are saved in the
theorems folder. Every theorem must import one file of the folder *definitions/god* and one of *definitions/entailment*.
To check how the different definitions affect the theorems just uncomment the appropriate imports or select the appropriate
file.

The same applies for the files in the *test* folder. All files here are to check if the abbreviations we made behave as we
would expect.

## Results (so far)
* godlike as a constant makes no sense
* collectionEntailment is necessary (individual entailment is not enough)
* godessentialConstNecessary can't be sledgehammered nor nitpicked (the reconstruction of oppys proof fails at some little steps)
* godessentialConst works out.
But Isabelle proofs it using awkward facts (different path than oppy). Maybe it exploits some errors. (not fully understood yet)
* We only investigated the proof of possible existence of god (not necessarily) since oppy did the same and then argued with the property of necessary existence. This is formalized in the absurdumTest in tests/collectionTests.thy but we are not sure if the formalization is suitable. (it fails)
