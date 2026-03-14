module xor_module_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic out_comb_logic
);
    // Output equals XOR of inputs each cycle.
    check_xor_function: assert property (
        @(posedge CLK) (out_comb_logic == (a ^ b))
    );

    // When inputs are equal, output is 0.
    check_out_zero_when_inputs_equal: assert property (
        @(posedge CLK) (a == b) |-> (out_comb_logic == 1'b0)
    );

    // When inputs differ, output is 1.
    check_out_one_when_inputs_unequal: assert property (
        @(posedge CLK) (a != b) |-> (out_comb_logic == 1'b1)
    );

    // When a is 0, output equals b.
    check_out_eq_b_when_a_zero: assert property (
        @(posedge CLK) (a == 1'b0) |-> (out_comb_logic == b)
    );

    // When a is 1, output equals ~b.
    check_out_eq_notb_when_a_one: assert property (
        @(posedge CLK) (a == 1'b1) |-> (out_comb_logic == ~b)
    );

    // When b is 0, output equals a.
    check_out_eq_a_when_b_zero: assert property (
        @(posedge CLK) (b == 1'b0) |-> (out_comb_logic == a)
    );

    // When b is 1, output equals ~a.
    check_out_eq_nota_when_b_one: assert property (
        @(posedge CLK) (b == 1'b1) |-> (out_comb_logic == ~a)
    );
endmodule