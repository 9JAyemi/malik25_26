module sky130_fd_sc_ms__fa_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic COUT,
    input logic SUM
);

    // SUM must equal the XOR of the three inputs.
    check_sum_equation: assert property (
        @(posedge clk) SUM == (A ^ B ^ CIN)
    );

    // COUT must equal the full-adder carry equation.
    check_cout_equation: assert property (
        @(posedge clk) COUT == ((A & B) | (B & CIN) | (A & CIN))
    );

    // All-zero inputs must produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CIN) |-> (!SUM && !COUT)
    );

    // All-one inputs must produce sum one and carry one.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && CIN) |-> (SUM && COUT)
    );

    // Exactly one high input must produce sum one and carry zero.
    check_one_hot_input_case: assert property (
        @(posedge clk)
        ((A && !B && !CIN) || (!A && B && !CIN) || (!A && !B && CIN))
        |-> (SUM && !COUT)
    );

    // Exactly two high inputs must produce sum zero and carry one.
    check_two_hot_input_case: assert property (
        @(posedge clk)
        ((A && B && !CIN) || (A && !B && CIN) || (!A && B && CIN))
        |-> (!SUM && COUT)
    );

    // When A and B are both high, carry must be asserted.
    check_ab_generates_carry: assert property (
        @(posedge clk) (A && B) |-> COUT
    );

    // When B and CIN are both high, carry must be asserted.
    check_bcin_generates_carry: assert property (
        @(posedge clk) (B && CIN) |-> COUT
    );

    // When A and CIN are both high, carry must be asserted.
    check_acin_generates_carry: assert property (
        @(posedge clk) (A && CIN) |-> COUT
    );

endmodule