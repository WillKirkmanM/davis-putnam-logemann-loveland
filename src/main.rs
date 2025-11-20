// DPLL SAT Solver in Rust
//
// This program implements a Boolean Satisfiability Solver using the 
// Davis-Putnam-Logemann-Loveland (DPLL) algorithm.
//
// It accepts a logical formula in Conjunctive Normal Form (CNF).
// Example: (x1 OR x2) AND (NOT x1 OR x3)

/// Represents a literal (variable or its negation).
/// Positive integer (e.g., 1) represents variable x1.
/// Negative integer (e.g., -1) represents NOT x1.
type Literal = i32;

/// A Clause is a disjunction (OR) of literals.
/// e.g., (x1 v x2 v !x3)
type Clause = Vec<Literal>;

/// A Formula is a conjunction (AND) of clauses.
/// e.g., C1 ^ C2 ^ C3
type Formula = Vec<Clause>;

/// The result of an assignment attempt.
#[derive(Debug, Clone, PartialEq)]
enum Status {
    Sat(Vec<Literal>), // Returns the list of literals assigned True
    Unsat,
}

/// The core recursive DPLL solver.
/// 
/// Returns Status::Sat(model) if a solution exists, Status::Unsat otherwise.
fn solve(mut formula: Formula) -> Status {
    let mut assignment: Vec<Literal> = Vec::new();

    // 1. Unit Propagation
    // Keep simplifying the formula as long as we find unit clauses (clauses with 1 literal).
    loop {
        // Check for empty clauses (conflict) -> UNSAT
        if formula.iter().any(|c| c.is_empty()) {
            return Status::Unsat;
        }

        // Check if formula is empty (all clauses satisfied) -> SAT
        if formula.is_empty() {
            return Status::Sat(assignment);
        }

        // Find a unit clause
        let unit_lit = formula.iter().find_map(|c| {
            if c.len() == 1 { Some(c[0]) } else { None }
        });

        match unit_lit {
            Some(lit) => {
                // Assign the forced literal
                assignment.push(lit);
                // Simplify formula based on this assignment
                formula = simplify_formula(&formula, lit);
            }
            None => break, // No more unit clauses, move to branching
        }
    }

    // 2. Branching (Splitting)
    // Pick the first literal of the first remaining clause to branch on.
    let pivot = formula[0][0];

    // Branch A: Assume pivot is TRUE
    let mut formula_true = formula.clone();
    formula_true = simplify_formula(&formula_true, pivot);
    
    match solve(formula_true) {
        Status::Sat(mut res) => {
            res.extend(assignment);
            res.push(pivot);
            return Status::Sat(res);
        }
        Status::Unsat => {
            // Branch A failed, try Branch B
            // Branch B: Assume pivot is FALSE (negate it)
            let mut formula_false = formula; // consume original
            formula_false = simplify_formula(&formula_false, -pivot);
            
            match solve(formula_false) {
                Status::Sat(mut res) => {
                    res.extend(assignment);
                    res.push(-pivot);
                    return Status::Sat(res);
                }
                Status::Unsat => Status::Unsat,
            }
        }
    }
}

/// Simplifies the formula assuming `lit` is TRUE.
/// 
/// Rules:
/// 1. If a clause contains `lit`, the clause is true. Remove it.
/// 2. If a clause contains `-lit`, that literal is false. Remove `-lit` from the clause.
fn simplify_formula(formula: &Formula, lit: Literal) -> Formula {
    let mut new_formula = Vec::with_capacity(formula.len());

    for clause in formula {
        // Rule 1: If clause contains lit, the whole clause is satisfied. Skip it.
        if clause.contains(&lit) {
            continue;
        }

        // Rule 2: If clause contains -lit, remove -lit from it.
        let neg_lit = -lit;
        if clause.contains(&neg_lit) {
            let mut new_clause = clause.clone();
            new_clause.retain(|&l| l != neg_lit);
            new_formula.push(new_clause);
        } else {
            // Clause is unaffected
            new_formula.push(clause.clone());
        }
    }

    new_formula
}

fn main() {
    println!("--- Rust SAT Solver (DPLL) ---");

    // Example Formula:
    // (x1 v x2) AND (x1 v x3) AND (!x1 v !x2) AND (!x3 v x2)
    //
    // In numbers:
    // 1. [1, 2]
    // 2. [1, 3]
    // 3. [-1, -2]
    // 4. [-3, 2]
    
    let formula: Formula = vec![
        vec![1, 2],
        vec![1, 3],
        vec![-1, -2],
        vec![-3, 2],
    ];

    println!("Solving for Formula: {:?}", formula);

    match solve(formula) {
        Status::Sat(model) => {
            println!("\nResult: SATISFIABLE");
            println!("Assignment Model:");
            // Sort for cleaner output
            let mut sorted_model = model.clone();
            sorted_model.sort_by_key(|a| a.abs());
            
            for lit in sorted_model {
                let val = if lit > 0 { "TRUE" } else { "FALSE" };
                println!("  Variable {}: {}", lit.abs(), val);
            }
        }
        Status::Unsat => {
            println!("\nResult: UNSATISFIABLE");
        }
    }
    
    println!("\n--- Example 2: Unsatisfiable Case (A AND !A) ---");
    let unsat_formula = vec![vec![1], vec![-1]];
    println!("Solving: {:?}", unsat_formula);
    if let Status::Unsat = solve(unsat_formula) {
         println!("Result: UNSATISFIABLE (As expected)");
    }
}

