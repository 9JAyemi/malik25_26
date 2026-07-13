module my_full_adder_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic CIN,
    input logic SUM,
    input logic COUT
);

    // Combinational DUT sampled on external clk; RTL has no reset.

    // SUM equals the XOR parity of A, B, and CIN.
    check_sum_parity: assert property (
        @(posedge clk) SUM == ((A ^ B) ^ CIN)
    );

    // COUT equals the implemented XOR chain of A, B, and CIN.
    check_cout_parity: assert property (
        @(posedge clk) COUT == ((A ^ B) ^ CIN)
    );

    // SUM and COUT are always identical in this RTL.
    check_outputs_identical: assert property (
        @(posedge clk) SUM == COUT
    );

    // Even input parity drives both outputs low.
    check_even_parity_low: assert property (
        @(posedge clk) !((A ^ B) ^ CIN) |-> ((SUM == 1'b0) && (COUT == 1'b0))
    );

    // Odd input parity drives both outputs high.
    check_odd_parity_high: assert property (
        @(posedge clk) ((A ^ B) ^ CIN) |-> ((SUM == 1'b1) && (COUT == 1'b1))
    );

endmodule