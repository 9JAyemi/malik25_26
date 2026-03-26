module sky130_fd_sc_lp__fa_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);

    // Outputs encode the 2-bit sum of A, B, and CIN.
    check_full_adder_encoding: assert property (
        @(posedge clk) {1'b0, COUT, SUM} == ({2'b00, A} + {2'b00, B} + {2'b00, CIN})
    );

    // Carry-out is high when at least two inputs are high.
    check_cout_majority: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CIN) | (B & CIN))
    );

    // Sum is the odd parity of the three inputs.
    check_sum_odd_parity: assert property (
        @(posedge clk) SUM == (A ^ B ^ CIN)
    );

    // All-low inputs produce zero carry and zero sum.
    check_zero_input_case: assert property (
        @(posedge clk) (!A && !B && !CIN) |-> (!COUT && !SUM)
    );

    // Exactly one high input produces sum without carry.
    check_single_one_case: assert property (
        @(posedge clk)
        ((A && !B && !CIN) || (!A && B && !CIN) || (!A && !B && CIN)) |-> (!COUT && SUM)
    );

    // Exactly two high inputs produce carry without sum.
    check_double_one_case: assert property (
        @(posedge clk)
        ((A && B && !CIN) || (A && !B && CIN) || (!A && B && CIN)) |-> (COUT && !SUM)
    );

    // All-high inputs produce both carry and sum.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CIN) |-> (COUT && SUM)
    );

endmodule