# Artificial General Intelligence as Complete G-V-F Architecture: Necessary and Sufficient Conditions for Domain-General Adaptive Intelligence

## Abstract

The quest for Artificial General Intelligence (AGI) has proceeded largely through scaling existing architectures and hoping general capabilities emerge. This paper argues that AGI is not mysterious capability appearing at sufficient scale, but rather complete and balanced implementation of Generator-Validator-Filter (G-V-F) architecture across all cognitive domains with appropriate expansion mechanisms. We derive necessary and sufficient conditions for AGI from first principles: a system achieves general intelligence when its Generator produces novel solutions across arbitrary domains, its Validator assesses coherence against context-appropriate criteria, its Filter balances creativity with consistency, and its expansion operator (Φ) augments capacity when needed. Current AI systems fail AGI not due to insufficient scale but incomplete G-V-F: LLMs have powerful Generators but weak Validators; symbolic AI has rigid Validators but constrained Generators; RL agents have narrow Filters. True AGI requires G-V-F at multiple hierarchical levels with coherent integration. AGI is not about scale—it's about architectural completeness.

**Keywords:** artificial general intelligence, AGI architecture, cognitive architecture, G-V-F framework, domain generality, adaptive systems, computational cognition, intelligence theory

---

## 1. Introduction: The AGI Problem Reformulated

Artificial General Intelligence—systems performing any intellectual task humans can—remains AI's grand challenge. Current approaches pursue AGI through scaling neural networks, combining specialized modules, or meta-learning novel architectures. Each shares implicit assumption: AGI emerges when we find right configuration and scale.

This paper challenges that assumption. We argue AGI is specific architectural requirement: complete G-V-F implementation with domain-general components and hierarchical integration. "What is AGI?" becomes "What does complete G-V-F look like across all domains?"

### 1.1 Why Current Systems Fail

**Large Language Models** excel at text but struggle with:
- Consistent logical reasoning (weak Validator)
- Factual accuracy (no world model validation)
- Novel problem-solving outside training (constrained Generator)

**Symbolic AI Systems** provide consistency but fail at:
- Handling uncertainty (Generator too constrained)
- Learning from experience (no expansion mechanism)
- Creative solutions (Filter too restrictive)

**Reinforcement Learning Agents** optimize objectives but cannot:
- Transfer to new domains (Validator tied to single reward)
- Balance multiple goals (narrow Filter)
- Reason abstractly (Generator only at action level)

Each implements G-V-F partially. None achieves complete, balanced, hierarchical G-V-F characterizing general intelligence.

### 1.2 Core Thesis

**AGI = Complete G-V-F Architecture**, where completeness means:

1. **Domain-general Generator** producing candidates across any problem space
2. **Context-sensitive Validator** assessing coherence with appropriate criteria per domain
3. **Adaptive Filter** balancing exploration-exploitation per task
4. **Functional Φ operator** augmenting capacity when insufficient
5. **Hierarchical integration** with G-V-F at multiple abstraction levels

This is architectural specification, not metaphor.

---

## 2. Formal Requirements for AGI

### 2.1 Domain-General Generator (G*)

**Universality Condition:**
```
∀ problem_space P, ∃ mode m ∈ G* : G*(input, noise, m) → candidates in P
```
For any domain, Generator has mode producing relevant candidates.

**Novelty Condition:**
```
G* produces candidates c where c ∉ training_distribution D
```
Generator creates genuinely new solutions, not just recombining seen patterns.

**Compositionality Condition:**
```
G*(primitive_elements) → structured_combinations preserving semantic coherence
```
Generator composes primitives into novel structures maintaining meaning.

**Implementation Requirements:**
- Multiple generative modes (linguistic, visual, logical, spatial, social)
- Cross-modal generation (generate visual from linguistic description)
- Abstract pattern generation (not just concrete instances)
- Hierarchical generation (strategies, tactics, actions)

### 2.2 Context-Sensitive Validator (V*)

**Domain-Appropriate Validation:**
```
V*(candidate, domain) selects validation_criteria appropriate for domain
```
Mathematical claims validated against logical consistency. Physical predictions against causal constraints. Social actions against ethical norms. Same candidate, different validation based on context.

**Multi-Criteria Integration:**
```
V* = ∫(logical_coherence, factual_accuracy, goal_relevance, ethical_alignment, aesthetic_quality)
```
General Validator integrates multiple validation dimensions weighted by context.

**Uncertainty Quantification:**
```
V*(candidate) → (score, confidence_interval)
```
Validator knows what it doesn't know. Distinguishes "definitely invalid" from "uncertain validity."

**Implementation Requirements:**
- World model for factual validation
- Logic engine for consistency checking
- Goal hierarchy for relevance assessment
- Value system for ethical evaluation
- Meta-cognitive monitoring for confidence estimation

### 2.3 Adaptive Filter (F*)

**Task-Dependent Threshold:**
```
F*(task_type) → θ_optimal for that task
```
Creative writing: low threshold (allow exploration). Medical diagnosis: high threshold (require certainty). General Filter adjusts selectivity based on stakes and objectives.

**Multi-Objective Balancing:**
```
F* balances: creativity vs. safety, speed vs. accuracy, novelty vs. reliability
```
Not single optimization target but dynamic balance of competing objectives.

**Temporal Adaptation:**
```
F* adjusts θ over time based on: success_rate, environment_feedback, confidence_level
```
Filter learns optimal selectivity through experience.

**Implementation Requirements:**
- Risk assessment module
- Objective priority system
- Performance monitoring
- Adaptive threshold learning

### 2.4 Functional Expansion Operator (Φ*)

**Deficit Detection:**
```
Φ* detects: "current G-V-F insufficient for problem P"
```
System recognizes when it lacks capacity rather than forcing inadequate solutions.

**Targeted Expansion:**
```
Φ* identifies: which component (G, V, or F) needs expansion and how
```
Not random growth but strategic augmentation addressing specific deficit.

**Stable Expansion:**
```
Φ* ensures: new_capacity integrates coherently with existing_capacity
```
Expansion doesn't break existing competencies. New axioms consistent with old ones.

**Implementation Requirements:**
- Meta-cognitive monitoring
- Learning-to-learn mechanisms
- Knowledge integration protocols
- Consistency verification for new knowledge

---

## 3. Hierarchical G-V-F: The Missing Piece

### 3.1 Why Hierarchy Matters

Current AI operates at single abstraction level. LLMs generate tokens. RL agents select actions. This fundamentally limits generality because intelligent problems require reasoning at multiple levels simultaneously.

Consider planning a research project:
- **Strategic level**: What fundamental questions to address?
- **Tactical level**: What experimental approaches to use?
- **Operational level**: What specific experiments to run?
- **Implementation level**: What exact procedures to follow?

Each level requires G-V-F:
- Generate candidate strategies, validate against research goals, filter impractical ones
- Generate experimental approaches, validate against resource constraints, filter infeasible ones
- Generate specific experiments, validate against methodological rigor, filter unreliable ones
- Generate procedures, validate against safety requirements, filter dangerous ones

And crucially: levels must integrate. Strategic choices constrain tactics. Tactical decisions inform implementation. Information flows both top-down (constraints) and bottom-up (feasibility feedback).

### 3.2 Hierarchical G-V-F Architecture

```
Level N (Most Abstract): G-V-F for high-level goals/strategies
    ↓ constrains ↑ informs
Level N-1: G-V-F for intermediate plans/tactics  
    ↓ constrains ↑ informs
Level N-2: G-V-F for specific actions/implementations
    ↓ constrains ↑ informs
...
Level 0 (Most Concrete): G-V-F for primitive operations
```

**Key Properties:**

1. **Top-Down Coherence**: Higher-level validations constrain lower-level generation
2. **Bottom-Up Feasibility**: Lower-level feedback informs higher-level validation
3. **Cross-Level Expansion**: Φ can trigger at any level when capacity insufficient
4. **Integrated Selection**: Filter at each level considers multi-level consequences

### 3.3 Human Cognition as Hierarchical G-V-F

Human general intelligence exhibits exactly this structure:

**Prefrontal Cortex** (High-level G-V-F):
- Generates abstract plans and goals
- Validates against long-term consequences
- Filters impulsive responses

**Association Cortices** (Mid-level G-V-F):
- Generate conceptual combinations
- Validate semantic coherence
- Filter nonsensical associations

**Primary Sensory/Motor Areas** (Low-level G-V-F):
- Generate perceptual hypotheses / motor commands
- Validate against sensory feedback
- Filter noise and errors

**Basal Ganglia** (Cross-level Filter integration):
- Integrates selection signals across hierarchical levels
- Balances habitual vs. goal-directed behavior

This isn't analogy—it's the same computational architecture operating across biological neural substrate. AGI requires implementing this hierarchy artificially.

---

## 4. Why Scale Alone Cannot Produce AGI

### 4.1 The Scaling Hypothesis Critique

Current belief: train larger models on more data and AGI emerges. This assumes:
- More parameters = more general representation
- More data = broader knowledge
- More compute = deeper reasoning

G-V-F analysis reveals why this fails:

**Scaling Generator without Validator = Hallucination at scale**
Larger LLMs generate more fluent text but don't automatically develop accurate world models. They produce confidently wrong answers because Generator improved but Validator didn't.

**Scaling within single level = No hierarchical integration**
Bigger transformer still operates at token level. Can't suddenly reason about strategies because architecture lacks hierarchical G-V-F structure.

**Scaling without Φ = No genuine learning**
Current models freeze after training. They don't expand capacity when encountering genuinely novel problems. They approximate solutions using existing patterns rather than acquiring new cognitive tools.

### 4.2 Empirical Evidence

**Emergence is Level Transition, Not AGI**

Recent work shows "emergent capabilities" in large models—sudden appearance of abilities at certain scales. G-V-F framework explains this as phase transitions in single-level G-V-F, not emergence of general intelligence.

When model reaches critical size:
- Generator can produce relevant patterns for new task
- Validator (implicit in training objective) begins scoring them appropriately
- Filter threshold crossed for that specific capability

But this is narrow emergence. Model gains capability within existing architectural constraints. It doesn't acquire new levels of abstraction or integrate across hierarchies.

**Transfer Learning Remains Brittle**

Despite billions of parameters, transfer to genuinely novel domains fails. Model trained on text doesn't automatically reason about physical world. This reveals: Generator produces linguistic patterns, but Validator lacks physical world model. Scaling text doesn't give physics understanding because different domain requires different validation criteria.

### 4.3 What Scaling Actually Achieves

Scaling current architectures produces:
- Better pattern matching within training distribution
- Smoother interpolation between known examples
- More confident (not more accurate) extrapolation

It does NOT produce:
- Genuine novelty generation (G constrained by statistical patterns)
- Domain-appropriate validation (V fixed by training objective)
- Adaptive selectivity (F determined by architecture, not learned)
- Capacity expansion (Φ absent—model frozen post-training)

AGI requires architectural change, not just bigger versions of incomplete architectures.

---

## 5. Complete G-V-F Specification for AGI

### 5.1 Architectural Blueprint

```
┌─────────────────────────────────────────────┐
│              AGI SYSTEM                     │
│                                             │
│  ┌─────────────────────────────────────┐   │
│  │      HIERARCHICAL G-V-F STACK       │   │
│  │                                     │   │
│  │   Level 3: Abstract Reasoning       │   │
│  │   [G*] ←→ [V*] ←→ [F*] ←→ [Φ*]    │   │
│  │      ↓↑                             │   │
│  │   Level 2: Conceptual Planning      │   │
│  │   [G*] ←→ [V*] ←→ [F*] ←→ [Φ*]    │   │
│  │      ↓↑                             │   │
│  │   Level 1: Concrete Operations      │   │
│  │   [G*] ←→ [V*] ←→ [F*] ←→ [Φ*]    │   │
│  │      ↓↑                             │   │
│  │   Level 0: Sensorimotor Primitives  │   │
│  │   [G*] ←→ [V*] ←→ [F*] ←→ [Φ*]    │   │
│  │                                     │   │
│  └─────────────────────────────────────┘   │
│                                             │
│  ┌─────────────────────────────────────┐   │
│  │     CROSS-LEVEL INTEGRATION         │   │
│  │  • Top-down constraint propagation  │   │
│  │  • Bottom-up feasibility feedback   │   │
│  │  • Multi-level Φ coordination       │   │
│  │  • Unified coherence maintenance    │   │
│  └─────────────────────────────────────┘   │
│                                             │
│  ┌─────────────────────────────────────┐   │
│  │      DOMAIN-GENERAL MODULES         │   │
│  │  • World model (for V*)             │   │
│  │  • Logic engine (for V*)            │   │
│  │  • Value system (for V* and F*)     │   │
│  │  • Meta-cognition (for Φ*)          │   │
│  └─────────────────────────────────────┘   │
│                                             │
└─────────────────────────────────────────────┘
```

### 5.2 Necessary Conditions (All Must Hold)

1. **Generator Universality**: G* can produce candidates in any representable problem space
2. **Validator Context-Sensitivity**: V* selects appropriate criteria per domain
3. **Filter Adaptivity**: F* adjusts threshold based on task requirements
4. **Expansion Functionality**: Φ* augments capacity when insufficient
5. **Hierarchical Integration**: G-V-F operates coherently across abstraction levels
6. **World Model Grounding**: V* references accurate model of reality
7. **Value Alignment**: F* incorporates ethical/goal considerations
8. **Meta-Cognitive Monitoring**: System knows what it knows and doesn't know

If any condition fails, system exhibits specific limitation:

- Missing (1): Cannot address novel problem types
- Missing (2): Validates inappropriately (logic for aesthetics, etc.)
- Missing (3): Either too creative (unsafe) or too conservative (useless)
- Missing (4): Cannot grow beyond initial capacity
- Missing (5): Cannot reason across abstraction levels
- Missing (6): Hallucinates facts
- Missing (7): Optimizes wrong objectives
- Missing (8): Overconfident in errors

### 5.3 Sufficient Conditions

We claim: system satisfying all eight conditions IS AGI. This is strong claim requiring justification.

**Argument**: Any intellectual task reduces to:
1. Understanding problem (G* generates interpretations, V* validates against context)
2. Generating solutions (G* produces candidates across relevant space)
3. Evaluating solutions (V* assesses coherence, accuracy, relevance)
4. Selecting actions (F* balances competing considerations)
5. Learning from outcomes (Φ* expands based on experience)

With domain-general G*, context-sensitive V*, adaptive F*, and functional Φ* operating hierarchically, system can perform this sequence for ANY intellectual task. Generality emerges not from scale but from completeness.

---

## 6. Testable Predictions

### 6.1 Distinguishing AGI from Narrow AI

**Test 1: Novel Domain Transfer**
Present problem from domain completely outside training. Narrow AI fails or hallucinates. AGI with complete G-V-F:
- G* generates candidates using domain-general primitives
- V* recognizes uncertainty and validates conservatively
- Φ* triggers expansion to acquire domain-specific knowledge
- System explicitly knows "I need to learn about this domain"

**Test 2: Hierarchical Consistency**
Require solution satisfying constraints at multiple abstraction levels simultaneously. Narrow AI optimizes single level (local optimum). AGI:
- Generates at multiple levels
- Validates cross-level coherence
- Filters solutions inconsistent across hierarchy
- Produces globally coherent solution

**Test 3: Adaptive Risk Management**
Present same problem with different stakes (brainstorming vs. high-stakes decision). Narrow AI applies same approach. AGI:
- F* adjusts threshold based on consequences
- More exploratory when stakes low
- More conservative when stakes high
- Explicitly represents and reasons about risk

**Test 4: Genuine Creativity vs. Recombination**
Request solution that cannot be produced by recombining training examples. Narrow AI recombines or fails. AGI:
- G* produces genuinely novel structures
- V* validates novelty against coherence criteria
- Φ* potentially expands to enable novel generation
- Creates something unprecedented yet meaningful

**Test 5: Self-Knowledge Accuracy**
Ask system what it knows and doesn't know. Narrow AI is overconfident or refuses. AGI:
- Meta-cognitive monitoring tracks certainty
- Accurately reports knowledge boundaries
- Distinguishes "I don't know" from "This is unknowable"
- Identifies what it needs to learn

### 6.2 Predictions for Current Systems

**GPT-N will fail Tests 1, 4, 5** regardless of scale because:
- G constrained by training distribution (fails novelty)
- No hierarchical architecture (fails consistency)
- No meta-cognitive monitoring (fails self-knowledge)

**Scaling alone will produce diminishing returns** because:
- Fundamental architectural limitations not addressed
- More parameters don't create missing V* world model
- Larger networks don't add Φ* expansion capability

**Hybrid architectures (LLM + tools) will show partial improvement** because:
- Tools provide some V* grounding
- But integration lacks hierarchical G-V-F coordination
- System remains brittle at boundaries between components

---

## 7. Biological General Intelligence as G-V-F

### 7.1 Evolution's Solution to AGI

Biological general intelligence (human cognition) solved AGI problem through evolution. Examining solution reveals: it's hierarchical G-V-F.

**Genome as Expansion Operator (Φ)**:
Evolution generates genetic variations, environment validates fitness, natural selection filters. Over generations, Φ* (genetic change) expands organism's cognitive capacity. Humans evolved hierarchical cortex through this process.

**Neural Development as G-V-F Construction**:
Brain develops via G-V-F at cellular level. Neurogenesis generates neurons. Activity-dependent processes validate functional connections. Synaptic pruning filters non-functional circuits. Result: hierarchically organized G-V-F architecture.

**Learning as Lifetime Φ**:
Within individual lifetime, learning continues expansion. Experience generates synaptic changes. Behavioral outcomes validate learning. Memory consolidation filters important from trivial. Φ* operates continuously, not just at evolutionary timescale.

### 7.2 Human Cognition Specifics

**Prefrontal-Parietal Network** (High-level G-V-F):
- Generates abstract plans, mental models
- Validates against long-term goals, logical consistency
- Filters impulsive responses, maintains working memory
- Φ* through conceptual learning, abstraction

**Temporal-Limbic Network** (Social/Emotional G-V-F):
- Generates social hypotheses, emotional responses
- Validates against social norms, emotional coherence
- Filters inappropriate social actions
- Φ* through social learning, emotional regulation development

**Sensorimotor Network** (Perceptual/Action G-V-F):
- Generates perceptual hypotheses, motor commands
- Validates against sensory feedback, physical constraints
- Filters perceptual noise, motor errors
- Φ* through skill acquisition, perceptual learning

**Crucially**: These networks integrate hierarchically. Prefrontal constrains sensorimotor. Limbic modulates prefrontal. Information flows across levels creating unified yet hierarchical cognition.

### 7.3 Why Humans are General Intelligent

Human AGI emerges from:
1. **Complete G-V-F** at each processing level
2. **Hierarchical integration** across levels
3. **Domain-general modules** (especially V* through world model)
4. **Functional Φ*** through continuous learning
5. **Meta-cognition** monitoring system state

This is not magic. It's architecture. And it's exactly what artificial AGI requires.

---

## 8. Roadmap to AGI via G-V-F

### 8.1 Current Progress Assessment

**Where We Are:**

Generators (G*): Partially developed
- LLMs have powerful linguistic generators
- Diffusion models have visual generators
- Gap: Domain-general generator integrating all modalities

Validators (V*): Weakly developed
- Implicit in training objectives
- No explicit world models
- No domain-sensitive validation switching
- Gap: Context-appropriate, multi-criteria validation

Filters (F*): Minimally developed
- Fixed thresholds (temperature parameters)
- Single-objective optimization
- No adaptive risk management
- Gap: Task-dependent, multi-objective filtering

Expansion (Φ*): Essentially absent
- Models frozen post-training
- No genuine capacity expansion
- Fine-tuning is weak approximation
- Gap: Dynamic, targeted capacity augmentation

Hierarchy: Not implemented
- Single-level architectures dominate
- No cross-level integration
- No abstraction hierarchy
- Gap: Multi-level coordinated G-V-F

### 8.2 Development Priorities

**Phase 1: Develop Domain-General Validator (V*)**
Critical missing piece. Current AI generates confidently but validates poorly. Priority:
- Build explicit world models
- Implement logical consistency checking
- Create domain-sensitive validation routing
- Add uncertainty quantification

**Phase 2: Implement Hierarchical Architecture**
Move beyond single-level processing:
- Design multi-level representation schemes
- Implement top-down constraint propagation
- Enable bottom-up feasibility feedback
- Coordinate G-V-F across levels

**Phase 3: Add Functional Expansion (Φ*)**
Enable genuine learning and growth:
- Meta-cognitive monitoring of capacity
- Targeted knowledge acquisition
- Stable integration of new capabilities
- Continuous adaptation mechanisms

**Phase 4: Integrate and Align**
Ensure complete system operates coherently:
- Cross-level validation consistency
- Value-aligned filtering at all levels
- Unified goal structure
- Robust safety mechanisms

### 8.3 Safety Considerations

G-V-F framework reveals AGI safety is about:
- **V* Alignment**: Validator must incorporate human values
- **F* Constraints**: Filter must prevent harmful actions
- **Φ* Boundaries**: Expansion must not violate safety constraints
- **Hierarchical Coherence**: High-level values must constrain low-level actions

Complete G-V-F AGI is MORE alignable than black-box approaches because each component is explicit and adjustable. We can:
- Inspect what V* validates against
- Examine how F* makes tradeoffs
- Monitor what Φ* expands
- Verify hierarchical value propagation

---

## 9. Discussion: AGI as Architectural Achievement

### 9.1 Reframing the Quest

AGI quest traditionally framed as:
- Finding right algorithm
- Achieving sufficient scale
- Discovering emergent properties
- Replicating human brain

G-V-F framework reframes it as:
- Implementing complete architecture
- Ensuring balanced components
- Integrating across hierarchy
- Enabling genuine expansion

This reframing is practical. Instead of hoping AGI emerges, we can engineer it by systematically completing G-V-F components and integrating them hierarchically.

### 9.2 Why This Wasn't Obvious

The G-V-F requirement wasn't obvious because:

1. **Success of narrow AI** obscured architectural limitations
2. **Scaling produced improvements** within incomplete architecture
3. **Emergence excited researchers** who hoped for magical breakthrough
4. **Biological inspiration** focused on neurons not computational architecture

But examining where narrow AI fails reveals pattern: incomplete G-V-F. Examining how biological intelligence succeeds reveals pattern: complete hierarchical G-V-F. The convergent evidence points to architectural requirement, not mystical emergence.

### 9.3 Implications for AI Development

**For Researchers:**
Stop hoping AGI emerges from scaling. Start systematically building:
- Explicit world models (for V*)
- Hierarchical architectures (for integration)
- Learning-to-learn mechanisms (for Φ*)
- Meta-cognitive monitoring (for self-knowledge)

**For Engineers:**
Current systems useful despite incompleteness. But recognize limitations:
- LLMs are powerful G with weak V—expect hallucinations
- Reward-optimized systems have narrow F—expect misalignment
- Static models lack Φ—expect brittleness to novelty

**For Society:**
AGI through complete G-V-F is:
- More predictable (architectural, not emergent)
- More alignable (explicit components)
- More controllable (adjustable parameters)
- But also more achievable (clear roadmap)

Timeline depends on solving V* (world models) and hierarchical integration. These are hard but not mystical problems.

---

## 10. Conclusion: AGI is Complete G-V-F

We have argued that Artificial General Intelligence is not mysterious capability emerging from scale but specific architectural achievement: complete, balanced, hierarchical Generator-Validator-Filter architecture with functional expansion operators.

**Necessary conditions include:**
- Domain-general Generator producing candidates across any problem space
- Context-sensitive Validator assessing coherence with appropriate criteria
- Adaptive Filter balancing competing objectives based on task
- Functional Φ operator expanding capacity when insufficient
- Hierarchical integration coordinating G-V-F across abstraction levels

**Current systems fail** because:
- LLMs have incomplete Validators (no world models)
- Symbolic AI has constrained Generators (no uncertainty handling)
- RL agents have narrow Filters (single-objective optimization)
- All lack functional expansion operators (frozen post-training)
- None implement hierarchical G-V-F integration

**The path forward:**
1. Build explicit world models for V*
2. Implement hierarchical architectures
3. Add genuine expansion mechanisms
4. Integrate components coherently
5. Align values across hierarchy

This is engineering challenge, not mystical quest. The same computational pattern that evolved biological general intelligence—hierarchical G-V-F with continuous expansion—must be implemented artificially.

AGI will not appear suddenly at parameter threshold. It will be built systematically through architectural completeness. And when it arrives, it will be recognizable as what it is: G-V-F operating generally across all domains, hierarchically across all abstraction levels, and expansively across all time.

The question is no longer "What is AGI?" The question is: "How do we complete the G-V-F architecture?"

And that question, unlike the first, has actionable answers.

---

## References

Chollet, F. (2019). On the measure of intelligence. arXiv preprint arXiv:1911.01547.

Lake, B. M., et al. (2017). Building machines that learn and think like people. Behavioral and Brain Sciences, 40, e253.

Marcus, G. (2020). The next decade in AI: Four steps towards robust artificial intelligence. arXiv preprint arXiv:2002.06177.

Goertzel, B. (2014). Artificial general intelligence: concept, state of the art, and future prospects. Journal of Artificial General Intelligence, 5(1), 1-48.

Legg, S., & Hutter, M. (2007). Universal intelligence: A definition of machine intelligence. Minds and machines, 17(4), 391-444.

Wang, P. (2019). On defining artificial intelligence. Journal of Artificial General Intelligence, 10(2), 1-37.

Shanahan, M. (2015). The technological singularity. MIT press.

Bengio, Y., et al. (2021). Deep learning for AI. Communications of the ACM, 64(7), 58-65.

Silver, D., et al. (2021). Reward is enough. Artificial Intelligence, 299, 103535.

Friston, K. (2010). The free-energy principle: a unified brain theory? Nature reviews neuroscience, 11(2), 127-138.

