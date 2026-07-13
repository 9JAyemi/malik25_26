module sky130_fd_sc_ms__xor3_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must equal the 3-input XOR of A, B, and C.
    check_x_matches_xor3: assert property (
        @(posedge clk) X === (A ^ B ^ C)
    );

    // 000 must drive X low.
    check_x_low_for_000: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0) && (C === 1'b0)) |-> (X === 1'b0)
    );

    // 001 must drive X high.
    check_x_high_for_001: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0) && (C === 1'b1)) |-> (X === 1'b1)
    );

    // 010 must drive X high.
    check_x_high_for_010: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b1) && (C === 1'b0)) |-> (X === 1'b1)
    );

    // 011 must drive X low.
    check_x_low_for_011: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b1) && (C === 1'b1)) |-> (X === 1'b0)
    );

    // 100 must drive X high.
    check_x_high_for_100: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b0) && (C === 1'b0)) |-> (X === 1'b1)
    );

    // 101 must drive X low.
    check_x_low_for_101: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b0) && (C === 1'b1)) |-> (X === 1'b0)
    );

    // 110 must drive X low.
    check_x_low_for_110: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1) && (C === 1'b0)) |-> (X === 1'b0)
    );

    // 111 must drive X high.
    check_x_high_for_111: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1) && (C === 1'b1)) |-> (X === 1'b1)
    );

endmodule