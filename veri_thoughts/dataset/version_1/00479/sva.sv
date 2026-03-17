module sky130_fd_sc_lp__ha_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic COUT,
    input logic SUM
);

    // COUT must implement the AND of A and B.
    check_cout_matches_and: assert property (
        @(posedge clk) COUT === (A & B)
    );

    // SUM must implement the XOR of A and B.
    check_sum_matches_xor: assert property (
        @(posedge clk) SUM === (A ^ B)
    );

    // When both inputs are 0, both outputs must be 0.
    check_zero_plus_zero: assert property (
        @(posedge clk)
        ((A === 1'b0) && (B === 1'b0)) |-> ((COUT === 1'b0) && (SUM === 1'b0))
    );

    // When exactly one input is 1, SUM must be 1 and COUT must be 0.
    check_one_hot_input_sum_only: assert property (
        @(posedge clk)
        (((A === 1'b0) && (B === 1'b1)) || ((A === 1'b1) && (B === 1'b0)))
        |-> ((COUT === 1'b0) && (SUM === 1'b1))
    );

    // When both inputs are 1, COUT must be 1 and SUM must be 0.
    check_one_plus_one_carry_only: assert property (
        @(posedge clk)
        ((A === 1'b1) && (B === 1'b1)) |-> ((COUT === 1'b1) && (SUM === 1'b0))
    );

endmodule