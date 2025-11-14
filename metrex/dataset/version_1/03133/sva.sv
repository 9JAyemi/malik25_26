// SVA checker for logic_function
module logic_function_sva (
    input A1, A2, B1, B2, C1, C2,
    input X
);
    // Local terms
    wire tA = A1 & A2;
    wire tB = B1 & B2;
    wire tC = C1 & C2;

    // Sanity: no X/Z on inputs and output
    a_no_xz_inputs: assert property (@(*)) !$isunknown({A1, A2, B1, B2, C1, C2});
    a_no_xz_output: assert property (@(*)) !$isunknown(X);

    // Functional correctness
    a_func_eq: assert property (@(*)) X == (tA | tB | tC);

    // Minimal but meaningful functional covers (all term-combinations)
    c_none:  cover property (@(*)) (!tA && !tB && !tC && !X);
    c_a:     cover property (@(*)) ( tA && !tB && !tC &&  X);
    c_b:     cover property (@(*)) (!tA &&  tB && !tC &&  X);
    c_c:     cover property (@(*)) (!tA && !tB &&  tC &&  X);
    c_ab:    cover property (@(*)) ( tA &&  tB && !tC &&  X);
    c_ac:    cover property (@(*)) ( tA && !tB &&  tC &&  X);
    c_bc:    cover property (@(*)) (!tA &&  tB &&  tC &&  X);
    c_abc:   cover property (@(*)) ( tA &&  tB &&  tC &&  X);
endmodule

// Bind into the DUT
bind logic_function logic_function_sva u_logic_function_sva (
    .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .C2(C2), .X(X)
);