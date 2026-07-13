module adder_4bit_carry_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    ///// Functional correctness /////
    // Combined {cout,sum} equals arithmetic a + b + cin (5-bit).
    check_addition_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // LSB sum matches XOR of a[0], b[0], and cin.
    check_sum_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // When inputs are all zero, outputs are zero.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) (a == 4'b0 && b == 4'b0 && cin == 1'b0) |-> (sum == 4'b0 && cout == 1'b0)
    );

    // Adding zero on b with cin=0 returns a and no carry.
    check_identity_b_zero_cin_zero: assert property (
        @(posedge clk) (b == 4'b0 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero on a with cin=0 returns b and no carry.
    check_identity_a_zero_cin_zero: assert property (
        @(posedge clk) (a == 4'b0 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

    // With b==0, result equals a + cin (proper 5-bit sum).
    check_b_zero_add_cin: assert property (
        @(posedge clk) (b == 4'b0) |-> ({cout, sum} == ({1'b0, a} + cin))
    );

    ///// Stability properties /////
    // If inputs are stable across a cycle, outputs remain stable.
    check_stable_inputs_hold_outputs: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({sum, cout})
    );

    // Outputs can change only if at least one input changed.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) $changed({sum, cout}) |-> $changed({a, b, cin})
    );

    ///// Corner cases /////
    // Max operands with cin=0 produce sum=14 and carry=1.
    check_max_plus_zero: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b0) |-> (sum == 4'he && cout == 1'b1)
    );

    // Max operands with cin=1 produce sum=15 and carry=1.
    check_max_plus_one: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> (sum == 4'hf && cout == 1'b1)
    );

    ///// Symmetry /////
    // Swapping a and b between cycles (with same cin) leaves {cout,sum} unchanged.
    check_commutativity_swap_invariance: assert property (
        @(posedge clk) (a == $past(b) && b == $past(a) && cin == $past(cin)) |-> ({cout, sum} == $past({cout, sum}))
    );

    // When a[0]==b[0], LSB of sum equals cin.
    check_lsb_when_a0_eq_b0: assert property (
        @(posedge clk) (a[0] == b[0]) |-> (sum[0] == cin)
    );
endmodule