module carry_select_adder_32bit_sva (
    input logic [31:0] A,
    input logic [31:0] B,
    input logic        Cin,
    input logic [31:0] S
);
    ///// Functional correctness /////
    // When Cin is 1, S equals bitwise XNOR of A and B.
    check_s_eq_xnor_when_cin_high: assert property (
        @(posedge Cin) disable iff (1'b0) (Cin) |-> (S == ~(A ^ B))
    );

    // When Cin is 0, S equals bitwise AND of A and B.
    check_s_eq_and_when_cin_low: assert property (
        @(negedge Cin) disable iff (1'b0) (!Cin) |-> (S == (A & B))
    );

    // When inputs are known (no X/Z), output S is known.
    check_s_known_when_inputs_known: assert property (
        @(posedge Cin) disable iff (1'b0) (!$isunknown({A,B,Cin})) |-> (!$isunknown(S))
    );

    ///// Useful special cases derived from the logic /////
    // With Cin=1 and A==B, S is all ones (XNOR true).
    check_allones_when_cin_high_and_a_eq_b: assert property (
        @(posedge Cin) disable iff (1'b0) (Cin && (A == B)) |-> (S == {32{1'b1}})
    );

    // With Cin=1 and A==~B, S is all zeros (XNOR false).
    check_allzeros_when_cin_high_and_a_eq_notb: assert property (
        @(posedge Cin) disable iff (1'b0) (Cin && (A == ~B)) |-> (S == 32'b0)
    );

    // With Cin=0 and B all ones, S equals A (A & all1 = A).
    check_s_eq_a_when_cin_low_and_b_allones: assert property (
        @(negedge Cin) disable iff (1'b0) (!Cin && (B == {32{1'b1}})) |-> (S == A)
    );

    // With Cin=0 and A all ones, S equals B (all1 & B = B).
    check_s_eq_b_when_cin_low_and_a_allones: assert property (
        @(negedge Cin) disable iff (1'b0) (!Cin && (A == {32{1'b1}})) |-> (S == B)
    );

    // With Cin=0 and either operand all zeros, S is all zeros.
    check_s_zero_when_cin_low_and_any_zero: assert property (
        @(negedge Cin) disable iff (1'b0) (!Cin && ((A == 32'b0) || (B == 32'b0))) |-> (S == 32'b0)
    );
endmodule