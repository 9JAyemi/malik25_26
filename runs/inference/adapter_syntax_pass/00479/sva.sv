module sky130_fd_sc_lp__ha_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SUM,
    input logic COUT
);

    // COUT is the AND of A and B.
    check_cout_is_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

    // SUM is the XOR of A and B.
    check_sum_is_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // The two outputs are never both high.
    check_outputs_not_both_high: assert property (
        @(posedge clk) !(COUT && SUM)
    );

    // When A and B are equal, both outputs are low.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk) (A == B) |-> (!COUT && !SUM)
    );

    // When A and B differ, COUT is low and SUM is high.
    check_different_inputs_drive_sum: assert property (
        @(posedge clk) (A != B) |-> (!COUT && SUM)
    );

endmodule