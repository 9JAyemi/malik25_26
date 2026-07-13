module binary_adder_shift_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic [1:0]  SHIFT,
    input logic [3:0]  S
);

    // No clock or reset exists in the RTL; clk is only a sampling clock.
    // The design is purely combinational: add A and B, then shift the low 4 sum bits.

    // The top output matches the add-then-shift datapath.
    check_top_level_function: assert property (
        @(posedge clk)
        (S == (SHIFT[1] ? {({1'b0, A} + {1'b0, B})[1:0], 2'b00} :
              (SHIFT[0] ? {({1'b0, A} + {1'b0, B})[2:0], 1'b0} :
                          {1'b0, ({1'b0, A} + {1'b0, B})[3:1]})))
    );

    // SHIFT[1] selects the two-bit left-shift result.
    check_shift2_full_mapping: assert property (
        @(posedge clk)
        (SHIFT[1]) |-> (S == {({1'b0, A} + {1'b0, B})[1:0], 2'b00})
    );

    // SHIFT=01 selects the one-bit left-shift result.
    check_shift1_full_mapping: assert property (
        @(posedge clk)
        (!SHIFT[1] && SHIFT[0]) |-> (S == {({1'b0, A} + {1'b0, B})[2:0], 1'b0})
    );

    // SHIFT=00 selects the one-bit right-shift result.
    check_shift_right_full_mapping: assert property (
        @(posedge clk)
        (!SHIFT[1] && !SHIFT[0]) |-> (S == {1'b0, ({1'b0, A} + {1'b0, B})[3:1]})
    );

    // The two-bit left shift always zero-fills the low bits.
    check_shift2_zero_fill: assert property (
        @(posedge clk)
        (SHIFT[1]) |-> (S[1:0] == 2'b00)
    );

    // The one-bit left shift always zero-fills bit 0.
    check_shift1_zero_fill: assert property (
        @(posedge clk)
        (!SHIFT[1] && SHIFT[0]) |-> (S[0] == 1'b0)
    );

    // The right shift always zero-fills bit 3.
    check_shift_right_zero_fill: assert property (
        @(posedge clk)
        (!SHIFT[1] && !SHIFT[0]) |-> (S[3] == 1'b0)
    );

    // When both SHIFT bits are high, SHIFT[1] has priority.
    check_shift11_priority: assert property (
        @(posedge clk)
        (SHIFT == 2'b11) |-> (S == {({1'b0, A} + {1'b0, B})[1:0], 2'b00})
    );

endmodule