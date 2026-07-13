module sky130_fd_sc_lp__ha_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B
);

    // COUT is the AND of A and B.
    check_cout_is_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

    // SUM is the XOR of A and B.
    check_sum_is_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // The two outputs are never high together.
    check_outputs_mutually_exclusive: assert property (
        @(posedge clk) !(COUT & SUM)
    );

    // When both inputs are low, both outputs are low.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) (!A && !B) |-> (!COUT && !SUM)
    );

    // When both inputs are high, both outputs are high.
    check_one_inputs_one_outputs: assert property (
        @(posedge clk) (A && B) |-> (COUT && SUM)
    );

    // When the inputs differ, SUM is high and COUT is low.
    check_different_inputs_xor: assert property (
        @(posedge clk) (A ^ B) |-> (SUM && !COUT)
    );

    // When the inputs are equal, SUM is low and COUT is low.
    check_equal_inputs_and: assert property (
        @(posedge clk) !(A ^ B) |-> (!SUM && !COUT)
    );

endmodule