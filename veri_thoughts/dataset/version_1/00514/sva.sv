module sky130_fd_sc_lp__fa_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);

    // Combined outputs match 1-bit addition of A, B, and CIN.
    check_full_adder_value: assert property (
        @(posedge clk) ({COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CIN}))
    );

    // Carry-out is the majority function of the three inputs.
    check_carry_majority: assert property (
        @(posedge clk) (COUT == ((A & B) | (A & CIN) | (B & CIN)))
    );

    // Sum is the odd-parity function of the three inputs.
    check_sum_odd_parity: assert property (
        @(posedge clk) (SUM == (A ^ B ^ CIN))
    );

    // All-zero inputs produce zero outputs.
    check_zero_inputs: assert property (
        @(posedge clk) ((!A && !B && !CIN) |-> ({COUT, SUM} == 2'b00))
    );

    // Exactly one asserted input produces sum without carry.
    check_single_high_input: assert property (
        @(posedge clk) ((({1'b0, A} + {1'b0, B} + {1'b0, CIN}) == 2'd1) |-> ({COUT, SUM} == 2'b01))
    );

    // Exactly two asserted inputs produce carry without sum.
    check_two_high_inputs: assert property (
        @(posedge clk) ((({1'b0, A} + {1'b0, B} + {1'b0, CIN}) == 2'd2) |-> ({COUT, SUM} == 2'b10))
    );

    // All-one inputs produce both carry and sum.
    check_all_high_inputs: assert property (
        @(posedge clk) ((A & B & CIN) |-> ({COUT, SUM} == 2'b11))
    );

endmodule