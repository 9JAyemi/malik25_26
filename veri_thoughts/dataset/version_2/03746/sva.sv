module full_adder_assertions (
    input logic clk,
    input logic a,
    input logic b,
    input logic cin,
    input logic s,
    input logic cout
);

    // Combinational RTL with no reset; sample on an external clock.

    // Sum is the XOR of all three inputs.
    check_sum_parity: assert property (
        @(posedge clk) s == (a ^ b ^ cin)
    );

    // Carry-out is high when at least two inputs are high.
    check_carry_majority: assert property (
        @(posedge clk) cout == ((a & b) | (a & cin) | (b & cin))
    );

    // The 2-bit result matches adding the three 1-bit inputs.
    check_result_matches_addition: assert property (
        @(posedge clk) {cout, s} == ({1'b0, a} + {1'b0, b} + {1'b0, cin})
    );

    // With cin low, the full adder reduces to a half adder.
    check_cin_zero_reduces_to_half_adder: assert property (
        @(posedge clk) (cin == 1'b0) |-> ((s == (a ^ b)) && (cout == (a & b)))
    );

    // With cin high, sum is inverted a^b and carry-out is a|b.
    check_cin_one_behavior: assert property (
        @(posedge clk) (cin == 1'b1) |-> ((s == ~(a ^ b)) && (cout == (a | b)))
    );

    // Stable inputs must keep outputs stable across sampled cycles.
    check_stable_inputs_imply_stable_outputs: assert property (
        @(posedge clk) $stable({a, b, cin}) |-> $stable({s, cout})
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) ({a, b, cin} == 3'b000) |-> ({cout, s} == 2'b00)
    );

    // All-one inputs produce sum one and carry one.
    check_all_one_case: assert property (
        @(posedge clk) ({a, b, cin} == 3'b111) |-> ({cout, s} == 2'b11)
    );

endmodule