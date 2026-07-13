module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CTRL,
    input logic [3:0] C
);

// In add mode, C equals A + B (4-bit wrap).
    check_add_mode_result: assert property (
        @(posedge clk) (CTRL == 1'b0) |-> (C == (A + B))
    );

// In shift mode, C equals {1'b0, A[3:1]} + {1'b0, B[3:1]} (4-bit wrap).
    check_shift_mode_result: assert property (
        @(posedge clk) (CTRL == 1'b1) |-> (C == ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

// In shift mode, C[3] is always 0 (no carry-out).
    check_shift_mode_msb_zero: assert property (
        @(posedge clk) (CTRL == 1'b1) |-> (C[3] == 1'b0)
    );

// In shift mode, C[2:0] equals A[2:0] + B[2:0].
    check_shift_mode_lsb3_to_0: assert property (
        @(posedge clk) (CTRL == 1'b1) |-> (C[2:0] == (A[2:0] + B[2:0]))
    );

// In add mode, 0 + 0 yields 0.
    check_add_zero_plus_zero: assert property (
        @(posedge clk) (CTRL == 1'b0 && A == 4'h0 && B == 4'h0) |-> (C == 4'h0)
    );

// In add mode, 0 + 15 yields 15.
    check_add_zero_plus_max: assert property (
        @(posedge clk) (CTRL == 1'b0 && A == 4'h0 && B == 4'hF) |-> (C == 4'hF)
    );

// In add mode, 15 + 0 yields 15.
    check_add_max_plus_zero: assert property (
        @(posedge clk) (CTRL == 1'b0 && A == 4'hF && B == 4'h0) |-> (C == 4'hF)
    );

// In add mode, 15 + 15 yields 30 (4-bit wrap to 2).
    check_add_max_plus_max: assert property (
        @(posedge clk) (CTRL == 1'b0 && A == 4'hF && B == 4'hF) |-> (C == 4'h2)
    );

// In shift mode, 0 + 0 yields 0.
    check_shift_zero_plus_zero: assert property (
        @(posedge clk) (CTRL == 1'b1 && A == 4'h0 && B == 4'h0) |-> (C == 4'h0)
    );

// In shift mode, 0 + 7 yields 0.
    check_shift_zero_plus_seven: assert property (
        @(posedge clk) (CTRL == 1'b1 && A == 4'h0 && B == 4'h7) |-> (C == 4'h0)
    );

// In shift mode, 7 + 0 yields 0.
    check_shift_seven_plus_zero: assert property (
        @(posedge clk) (CTRL == 1'b1 && A == 4'h7 && B == 4'h0) |-> (C == 4'h0)
    );

// In shift mode, 7 + 7 yields 0.
    check_shift_seven_plus_seven: assert property (
        @(posedge clk) (CTRL == 1'b1 && A == 4'h7 && B == 4'h7) |-> (C == 4'h0)
    );

endmodule
