module full_adder_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // Outputs match the 2-bit sum of the three 1-bit inputs.
    check_output_matches_addition: assert property (
        @(posedge clk)
        {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CI})
    );

    // SUM is the odd-parity function of A, B, and CI.
    check_sum_is_input_parity: assert property (
        @(posedge clk)
        SUM == (A ^ B ^ CI)
    );

    // COUT is high when at least two inputs are high.
    check_cout_is_majority: assert property (
        @(posedge clk)
        COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // All-zero inputs produce zero outputs.
    check_zero_inputs: assert property (
        @(posedge clk)
        (!A && !B && !CI) |-> ({COUT, SUM} == 2'b00)
    );

    // All-one inputs produce both outputs high.
    check_all_one_inputs: assert property (
        @(posedge clk)
        (A && B && CI) |-> ({COUT, SUM} == 2'b11)
    );

    // Exactly one high input produces SUM only.
    check_one_high_input: assert property (
        @(posedge clk)
        (( A && !B && !CI) ||
         (!A &&  B && !CI) ||
         (!A && !B &&  CI)) |-> ({COUT, SUM} == 2'b01)
    );

    // Exactly two high inputs produce COUT only.
    check_two_high_inputs: assert property (
        @(posedge clk)
        (( A &&  B && !CI) ||
         ( A && !B &&  CI) ||
         (!A &&  B &&  CI)) |-> ({COUT, SUM} == 2'b10)
    );

endmodule