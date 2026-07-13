module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [1:0] shift,
    input logic [1:0] shift_amount,
    input logic select,
    input logic [3:0] Q
);
    // Clock: clk, Reset: reset (active-low async). Top Q is a comb mux of registered submodule outputs.

    // Q must be zero during active-low reset.
    check_reset_clears_Q: assert property (
        @(posedge clk) !reset |-> (Q == 4'b0000)
    );

    // When select=0 and shift_amount=00, Q passes A.
    check_sel0_sa00_passthru: assert property (
        @(posedge clk) disable iff (!reset) (!select && (shift_amount == 2'b00)) |-> (Q == A)
    );

    // When select=0 and shift_amount=01, Q = {A[2:0], A[3]}.
    check_sel0_sa01_rotl1: assert property (
        @(posedge clk) disable iff (!reset) (!select && (shift_amount == 2'b01)) |-> (Q == {A[2:0], A[3]})
    );

    // When select=0 and shift_amount=10, Q = {A[3], A[3:1]} (arith right 1).
    check_sel0_sa10_sra1: assert property (
        @(posedge clk) disable iff (!reset) (!select && (shift_amount == 2'b10)) |-> (Q == {A[3], A[3:1]})
    );

    // When select=0 and shift_amount=11, Q = {A[2:0], A[3]}.
    check_sel0_sa11_rotl1: assert property (
        @(posedge clk) disable iff (!reset) (!select && (shift_amount == 2'b11)) |-> (Q == {A[2:0], A[3]})
    );

    // When select=1 and shift=00, Q passes A.
    check_sel1_s00_passthru: assert property (
        @(posedge clk) disable iff (!reset) (select && (shift == 2'b00)) |-> (Q == A)
    );

    // When select=1 and shift=11, Q = {A[2:0], A[3]}.
    check_sel1_s11_rotl1: assert property (
        @(posedge clk) disable iff (!reset) (select && (shift == 2'b11)) |-> (Q == {A[2:0], A[3]})
    );

    // When select=1 and shift=01, upper bits of Q come from A[2:0].
    check_sel1_s01_upper_from_A: assert property (
        @(posedge clk) disable iff (!reset) (select && (shift == 2'b01)) |-> (Q[3:1] == A[2:0])
    );

    // When select=1 and shift=01, Q[0] comes from prev shift_output[3].
    check_sel1_s01_lsb_from_prev_shift3: assert property (
        @(posedge clk) disable iff (!reset)
            (select && (shift == 2'b01) && $past(reset))
        |-> (Q[0] ==
             ( (($past(shift_amount) == 2'b01) || ($past(shift_amount) == 2'b11))
               ? $past(A[2]) : $past(A[3]) ))
    );

    // When select=1 and shift=10, lower bits of Q come from A[3:1].
    check_sel1_s10_lower_from_A: assert property (
        @(posedge clk) disable iff (!reset) (select && (shift == 2'b10)) |-> (Q[2:0] == A[3:1])
    );

    // When select=1 and shift=10, Q[3] comes from prev shift_output[0].
    check_sel1_s10_msb_from_prev_shift0: assert property (
        @(posedge clk) disable iff (!reset)
            (select && (shift == 2'b10) && $past(reset))
        |-> (Q[3] ==
             ( ($past(shift_amount) == 2'b00) ? $past(A[0]) :
               (($past(shift_amount) == 2'b10) ? $past(A[1]) : $past(A[3])) ))
    );

endmodule