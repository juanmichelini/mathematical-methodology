// The method as the thesis presents it (Foundations for Mathematical Methodology, J. Michelini, 2016),
// section by section, each with the Lean source that implements that part.  The thesis text is
// quoted; `lean` lists the declarations to show: the build extracts them from the repository by
// name and fails if one is missing.  `note` is this site's own commentary on how the Lean version
// differs from the thesis' Haskell.

export const THESIS = {
  title: 'Foundations for Mathematical Methodology',
  author: 'Juan Michelini',
  year: 2016,
  school: 'Universidad ORT Uruguay',
};

export const SECTIONS = [
  {
    id: 'levels',
    num: '1, 5',
    title: 'Three levels',
    thesis: [
      'We consider the work of mathematicians to be mathematical theories, that is, collections of proofs. Mathematicians must 1) decide what to attempt to prove 2) attempt to prove it 3) stay on top of all the chores that follow from the other two. [...] We will name each of this divisions of work as (1) strategical, (2) tactical and (3) operational.',
      'As we have mentioned, we will divide the method into three levels: the strategical, the tactical and the operational. That is: “What to prove”, “How to prove” and “How to do everything else needed”. Like in the traditional mathematical education we will start with the operational (how to check for equality, how to substitute), then go into the tactical (when to apply a lemma, when to carry induction) and finally into the strategical (which theorems are interesting).',
    ],
    note:
      'The Lean code is split the same way. The table lists the modules of each level, with their size computed from the repository.',
    levels: true,
  },
  {
    id: 'language',
    num: '4',
    title: 'A variant of typed λ-calculus',
    thesis: [
      'Our chosen language is a variant of typed λ-calculus, it is also a subset of the Haskell programming language, which belongs to the ML family. It only allows recursive functions, finite types (like Bool), inductive types (like N) and inductive parametric types (like (List a), i.e. lists of any fixed type a). [...] To manipulate values we may use the case construct. To simplify matters we will not allow pattern matching or classes. [...] To simplify matters even further, we will only consider primitive recursion.',
      'We will only consider propositions of the form ··· = ···. That is, we will only consider equalities among expressions of one and the same type where all the variables are quantified with a ∀.',
    ],
    code: 'sum :: N → N → N\nsum = λx.λy. case x of {\n           Z → y;\n           S j → S(sum j y)\n           }',
    codeCaption: 'The thesis’ definition of addition',
    note:
      'In Lean the terms are de Bruijn terms (no variable names); the names the thesis prints are kept as metadata and rebuilt for display. The same addition, exported by the system as plain Lean, is shown below.',
    lean: [
      { file: 'MathematicalMethodology/Operational/Term.lean', symbol: 'Term', caption: 'Terms' },
      { file: 'MathematicalMethodology/Operational/Term.lean', symbol: 'Alts', caption: 'The alternatives of a case' },
      { file: 'MathematicalMethodology/Strategic/Syntax.lean', symbol: 'Ty', caption: 'Types' },
      { file: 'MathematicalMethodology/Generated/Suite.lean', symbol: 'suma', caption: 'Addition, as the system exports it (plain Lean)', generated: true },
    ],
  },
  {
    id: 'operations',
    num: '6',
    title: 'Operations permit',
    thesis: [
      'The operational level defines what it is possible. It defines all the possible actions we could take. What we can and cannot do. It permits certain actions and denies others. To our purposes this level contains everything needed for the proper care of syntax. This level includes for example recognizing when there is a type error (i.e. whether an expression compiles), writing a primitive schema of recursion from a type definition, applying a β-rule, recognizing where a lemma can be applied regardless of whether it is desirable to do so.',
    ],
    note: 'Substitution, β-reduction, case reduction and unfolding definitions. This level is the trusted base.',
    lean: [
      { file: 'MathematicalMethodology/Operational/Term.lean', symbol: 'Term.subst', caption: 'Substitution' },
      { file: 'MathematicalMethodology/Operational/Term.lean', symbol: 'Term.beta', caption: 'β-rule' },
      { file: 'MathematicalMethodology/Operational/Compute.lean', symbol: 'Term.step', caption: 'One computation step' },
    ],
  },
  {
    id: 'tactics',
    num: '7',
    title: 'Tactics prove',
    thesis: [
      'The tactical level defines how we attempt things. In the operational level we just do. In the tactical level we do in order to. Choice, desire and the risk of failure come into play. Tactics are operations tagged with a purpose that might fail.',
      'To solve this we structured our main tactic, composed of five minor tactics, in such a way as to eliminate, as much as possible, the need for backtracking. By only undoing the current step, and never previous ones, we can proceed without the need for drafts.',
      'Our main tactic is composed of five tactics which are tried in turn. If one succeeds, we reapply the main tactic to all the new conjectures that arise, otherwise we try with the next one. If all the five tactics fail, the attempt fails. The tactics are Trivialize, Compute, Fundamentalize, Reorder and Induction.',
    ],
    note:
      'This is the thesis’ main tactic: the five tactics tried in turn, in this order. A proof is a tree whose steps carry the comment that justifies them, which is what the result pages print in the thesis’ format.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'mainTactic', caption: 'The main tactic' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'Proof', caption: 'A proof is a tree' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'Comment', caption: 'The comment on each step' },
    ],
  },
  {
    id: 'trivialize',
    num: '7.1',
    title: 'Trivialize',
    thesis: [
      'Trivialize is the easiest tactic and the only one that can succeed without generating more work. Given a theorem of the form α = β it returns success with the empty list if α and β differ only in the names of the bound variables. Otherwise, it fails.',
    ],
    note: 'With de Bruijn terms, α-equivalence is syntactic equality: the first line of the main tactic.',
    snippet: {
      file: 'MathematicalMethodology/Tactical/Prove.lean',
      after: /if c\.aff\.lhs == c\.aff\.rhs then/,
      count: 1,
      caption: 'Trivialize (first branch of mainTactic)',
    },
  },
  {
    id: 'compute',
    num: '7.2',
    title: 'Compute',
    thesis: [
      'Computing, i.e. solving redexes, has the benefit of reducing the formulas to a normal form. This increases the chance of succeeding with Trivialize. We should be careful not to complicate matters for the other tactics by making the resulting formulas more complex. To fix this, we will only solve redexes when we can do so without ending in a case construct or a lambda expression.',
    ],
    note: 'It computes on both sides, and refuses results that end in a case or a lambda.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'computeDontEndInCas', caption: 'Compute, one side' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'bothSides', caption: 'Compute, both sides' },
    ],
  },
  {
    id: 'fundamentalize',
    num: '7.3',
    title: 'Fundamentalize',
    thesis: [
      'This is the first tactic that considers lemmas and hypotheses. [...] We want to, whenever possible, use lemmas as rewriting rules. To do so we have to choose the direction in which to apply the lemma. That is, given α = β, we want to transform it to either α → β or β → α. When it is obvious that the proper way to apply the lemma is α → β we say that β is more fundamental than α.',
      'Taking this into account, we propose a formalization of fundamentality as an index, in such a way that the lower the index, the more fundamental the expression. Constructors have a fundamentality of 1. Bound variables a fundamentality of 0. Variables names defined in the environment have the fundamentality of their definition. [...] Sorting the list of lemmas is reduced to counting, and applying a lemma is reduced to trying the lemmas in the sorted list in turn.',
    ],
    note:
      'fund is computed with explicit fuel so that the definition is structurally terminating (unfolding a definition removes it from the environment). HRec.add is the sorted list of lemmas: it decides the direction of each new lemma by comparing fundamentalities.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Store.lean', symbol: 'Term.fundF', caption: 'Fundamentality' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'HRec.add', caption: 'Adding a lemma: choosing its direction' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'applyRecH', caption: 'Applying the stored lemmas in turn' },
    ],
  },
  {
    id: 'reorder',
    num: '7.4',
    title: 'Reorder',
    thesis: [
      'If we consider the lemma sum x y = sum y x in isolation, any direction would be arbitrary. If it cannot depend on the lemma, it must depend on the expression we apply the lemma to. If we are in a situation where we can apply such a lemma we will do so only if it results in a smaller expression under some (arbitrary) order.',
    ],
    note: 'permutaC recognises a lemma that only permutes atoms; such lemmas go to the reordering list and are applied only when they decrease the order.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'permutaC', caption: 'A lemma that only reorders' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'masOrdNN', caption: 'The order on expressions' },
    ],
  },
  {
    id: 'induction',
    num: '7.5',
    title: 'Induction',
    thesis: [
      'If everything else fails, but there is at least one quantified variable, we can apply primitive induction. This tactic is the reason that tactics return a lists of new conjectures to prove, one for each case, each with its own hypotheses. [...] A good tactic is to consider the definitions of the functions involved, and to only apply induction on a variable which will allow us to perform computation on all the cases.',
    ],
    note: 'Induction on the first variable; each case comes with its induction hypotheses as new lemmas for the store.',
    lean: [{ file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'indcFst', caption: 'Induction' }],
  },
  {
    id: 'proof',
    num: '7.6',
    title: 'Carrying out a proof',
    thesis: [
      'We will attempt to prove by hand the following theorem: length (append xs ys) = sum (length xs) (length ys) [...] Beginning the proof, we notice that all first four tactics fail so we apply induction. Applying induction on xs allows Compute to succeed in all cases on both sides of the equality.',
      'Although our chosen presentation is quite verbose, the detail can be adjusted as necessary.',
    ],
    note:
      'Below, a proof the system found, printed in the thesis’ format, next to the Lean theorem the same proof was exported to. prove runs the main tactic with the thesis’ budget (“patience”) and cuts the attempt when it is spent.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'prove', caption: 'Carrying out a proof' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'giveUp', caption: 'Giving up when the budget is spent' },
    ],
    exampleProof: { fn: 'f3', statement: 'a:C_,a_R |- f3 (f3 a) = a', title: 'The reverse function is its own inverse' },
  },
  {
    id: 'data',
    num: '8.1',
    title: 'Proposing data types',
    thesis: [
      'As we have said we care about enumerated types like Bool, inductive types like N and inductive parametric types like List a. Notice that we care about the structure of the type, not of its name. To avoid wasted efforts reinventing the wheel we consider canonical names for types. [...] All type names are a list of the parameters of their constructors separated by “,”. If a constructor has no parameters we use a “_”. If the parameter is recursive we use an “R”. If the parameter is any other fixed type we use a lowercase letter.',
    ],
    note: 'The enumeration is a port of the thesis’ Propose module. The canonical names are kept; Lean identifiers are the injective sanitisation of them (_ ↦ _u, “,” ↦ _c, “.” ↦ _d).',
    lean: [
      { file: 'MathematicalMethodology/Strategic/Enumerate.lean', symbol: 'enumContainerRecTypes', caption: 'Enumerating inductive types' },
      { file: 'MathematicalMethodology/Strategic/Enumerate.lean', symbol: 'datas', caption: 'The data types proposed' },
    ],
    dataTypes: true,
  },
  {
    id: 'functions',
    num: '8.2',
    title: 'Proposing functions',
    thesis: [
      'To propose functions we must first choose those types we are interested in. [...] After proposing a type, we choose on which of its parameters we want to apply the schema of recursion. This gives us a schema of recursion to be filled in. Once the filling is done, we get a function. [...] Here some heuristics are useful: (1) we must use at least one recursive call if available (2) we will avoid using the same subexpression more than twice (3) we will try to keep the fundamentality score of the function as low as possible (which usually means reducing the use of auxiliary functions to the minimum).',
    ],
    note: 'The first search proposes the 64 functions over N; the second search proposes 164 more using the functions the first one kept. Counts are read from the generated files.',
    lean: [
      { file: 'MathematicalMethodology/Strategic/Enumerate.lean', symbol: 'candidatosFst', caption: 'Candidate functions, first search' },
      { file: 'MathematicalMethodology/Strategic/SecondSearch.lean', symbol: 'candidatosSnd', caption: 'Candidate functions, second search' },
    ],
  },
  {
    id: 'conjectures',
    num: '8.3',
    title: 'Proposing conjectures',
    thesis: [
      'We do not care about all theorems, we only care about those theorems that increase our tactical or strategical ability. A theorem is ample if we can apply it in a great number of situations. [...] When faced with a new function we first propose ample conjectures. The question we are trying to answer is: how can I maneuver when I encounter this function in the future?',
      'If we succeed in proving many properties about a function, we consider it interesting. So we use it as a base to propose more functions and more equations.',
    ],
    note:
      'findlemas proposes the conjectures for a function, drops the ones a stored lemma already rewrites (“we do not suggest x + 0 + 0 = x if we have already proved that x + 0 = x”), and proves them in order, each new lemma joining the store.',
    lean: [
      { file: 'MathematicalMethodology/Strategic/Conjecture.lean', symbol: 'plemas', caption: 'Proposing the conjectures of a function' },
      { file: 'MathematicalMethodology/Strategic/FindLemmas.lean', symbol: 'findlemas', caption: 'Finding the lemmas of a function' },
      { file: 'MathematicalMethodology/Tactical/Prove.lean', symbol: 'provell', caption: 'Proving the batches in order' },
    ],
  },
  {
    id: 'implementation',
    num: '9',
    title: 'Implementation as a computer program',
    thesis: [
      'We have implemented the informal method described above as a computer program. We have done so to convince ourselves that the method is purely external. The implementation also serves as a formal specification, the previous exposition of the method, by virtue of being informal, might have omissions or ambiguities. No such thing can happen in the code.',
      'We have specified the syntax and semantics of our language in the modules Compute, Syntax and Type. We have specified the tactical level in the Prove module. We have specified the strategical level in the Propose module. The operational level is scattered all over.',
    ],
    note: 'Where each Haskell module of the thesis went. Line counts are computed from the repository.',
    modules: [
      { thesis: 'Compute, Syntax, Type', lean: ['MathematicalMethodology/Operational/Term.lean', 'MathematicalMethodology/Operational/Compute.lean', 'MathematicalMethodology/Strategic/Syntax.lean'] },
      { thesis: 'Prove (mainTactic, triv, applyRec, addAffirms, indc, fund)', lean: ['MathematicalMethodology/Tactical/Prove.lean', 'MathematicalMethodology/Tactical/Store.lean'] },
      { thesis: 'Propose (enumContainerRecTypes, enumTip, findlemas)', lean: ['MathematicalMethodology/Strategic/Enumerate.lean', 'MathematicalMethodology/Strategic/Conjecture.lean', 'MathematicalMethodology/Strategic/FindLemmas.lean'] },
      { thesis: 'Main (the two searches)', lean: ['MathematicalMethodology/Strategic/FirstSearch.lean', 'MathematicalMethodology/Strategic/SecondSearch.lean'] },
      { thesis: 'Test (the lemma suite, exponentiation)', lean: ['MathematicalMethodology/Examples/TestSuite.lean', 'MathematicalMethodology/Examples/TestEnv.lean'] },
    ],
  },
  {
    id: 'beyond',
    num: '—',
    title: 'What the Lean version adds',
    thesis: [
      'A glaring omission from our work is proving the correspondence between the informal internal definition and the formal external one. [...] but it is hard to convince ourselves that they represent the same method.',
    ],
    note:
      'The thesis leaves two things open that the Lean version addresses. (1) A small trusted checker: tactics that find proofs are untrusted, and a certificate checker accepts only correct ones, with a proof of its soundness. (2) Every proof the system finds is exported as a Lean theorem and checked by Lean itself, in CI; if one does not compile, the build fails.',
    lean: [
      { file: 'MathematicalMethodology/Tactical/Cert.lean', symbol: 'Cert', caption: 'Proof certificates' },
      { file: 'MathematicalMethodology/Semantics/CheckSound.lean', symbol: 'Cert.check_sound', caption: 'The checker is sound (statement; the proof is in the file)', stop: /^\s{4}\| \./ },
    ],
  },
];
