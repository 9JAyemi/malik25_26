module adder4_sva (
    input logic cin,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum,
    input logic cout
);
    // Outputs equal the 5-bit sum of inputs.
    check_full_sum_match: assert property (
        @(posedge $global_clock) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // sum is the lower 4 bits of the 5-bit sum.
    check_sum_lower_bits: assert property (
        @(posedge $global_clock) sum == (({1'b0, a} + {1'b0, b} + cin)[3:0])
    );

    // cout is the MSB of the 5-bit sum.
    check_cout_is_msb: assert property (
        @(posedge $global_clock) cout == (({1'b0, a} + {1'b0, b} + cin)[4])
    );

    // If the 5-bit sum is less than 16, cout must be 0.
    check_no_carry_when_no_overflow: assert property (
        @(posedge $global_clock) (({1'b0, a} + {1'b0, b} + cin) < 5'd16) |-> (cout == 1'b0)
    );

    // If the 5-bit sum is at least 16, cout must be 1.
    check_carry_when_overflow: assert property (
        @(posedge $global_clock) (({1'b0, a} + {1'b0, b} + cin) >= 5'd16) |-> (cout == 1'b1)
    );

    // With zero inputs, sum equals cin in bit0 and cout is 0.
    check_zero_inputs_behavior: assert property (
        @(posedge $global_clock) (a == 4'b0000 && b == 4'b0000) |-> (sum == {3'b000, cin} && cout == 1'b0)
    );

    // When cin is 0, result equals a+b (5-bit).
    check_cin_zero_case: assert property (
        @(posedge $global_clock) (cin == 1'b0) |-> ({cout, sum} == ({1'b0, a} + {1'b0, b}))
    );

    // When cin is 1, result equals a+b+1 (5-bit).
    check_cin_one_case: assert property (
        @(posedge $global_clock) (cin == 1'b1) |-> ({cout, sum} == ({1'b0, a} + {1'b0, b} + 5'd1))
    );

    // If inputs are stable cycle-to-cycle, outputs must be stable.
    check_stable_outputs_when_inputs_stable: assert property (
        @(posedge $global_clock) $stable({a, b, cin}) |-> $stable({sum, cout})
    );

    // Max inputs with cin=0 produce 30 => sum=14, cout=1.
    check_max_inputs_cin0: assert property (
        @(posedge $global_clock) (a == 4'hF && b == 4'hF && cin == 1'b0) |-> (sum == 4'hE && cout == 1'b1)
    );

    // Max inputs with cin=1 produce 31 => sum=15, cout=1.
    check_max_inputs_cin1: assert property (
        @(posedge $global_clock) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> (sum == 4'hF && cout == 1'b1)
    );
endmodule