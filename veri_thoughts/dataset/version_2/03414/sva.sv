module sky130_fd_sc_ls__fahcin_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);

    // SUM matches A xor B xor inverted CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

    // COUT matches the majority of A, B, and inverted CIN.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

    // If both A and B are high, COUT must be high.
    check_cout_when_ab_high: assert property (
        @(posedge clk) (A && B) |-> COUT
    );

    // If both A and B are low, COUT must be low.
    check_cout_when_ab_low: assert property (
        @(posedge clk) (!A && !B) |-> !COUT
    );

    // With exactly one of A or B high, COUT follows inverted CIN.
    check_cout_single_high_input: assert property (
        @(posedge clk) (A ^ B) |-> (COUT == ~CIN)
    );

    // With equal A and B, SUM follows inverted CIN.
    check_sum_equal_inputs: assert property (
        @(posedge clk) !(A ^ B) |-> (SUM == ~CIN)
    );

    // With different A and B, SUM follows CIN.
    check_sum_different_inputs: assert property (
        @(posedge clk) (A ^ B) |-> (SUM == CIN)
    );

    // When CIN is high, SUM is XOR and COUT is AND of A and B.
    check_cin_high_behavior: assert property (
        @(posedge clk) CIN |-> ((SUM == (A ^ B)) && (COUT == (A & B)))
    );

    // When CIN is low, SUM is XNOR and COUT is OR of A and B.
    check_cin_low_behavior: assert property (
        @(posedge clk) !CIN |-> ((SUM == ~(A ^ B)) && (COUT == (A | B)))
    );

endmodule