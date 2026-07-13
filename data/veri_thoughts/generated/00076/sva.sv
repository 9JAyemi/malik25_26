module top_module_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [1:0]  shift_amount,
    input logic        shift_dir,
    input logic        enable,
    input logic [1:0]  select,
    input logic [15:0] out
);

    // Sampled with an external formal clock; the RTL has no native clock or reset.

    // Bits [11:4] are always zero in the top-level output composition.
    check_middle_bits_zero: assert property (
        @(posedge clk) out[11:4] == 8'h00
    );

    // A zero shift passes A through to the upper nibble.
    check_no_shift_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (out[15:12] == A)
    );

    // A left shift by 1 zero-fills the LSB.
    check_left_shift_by_1: assert property (
        @(posedge clk) ((shift_dir == 1'b1) && (shift_amount == 2'b01)) |-> (out[15:12] == {A[2:0], 1'b0})
    );

    // A left shift by 2 zero-fills the two LSBs.
    check_left_shift_by_2: assert property (
        @(posedge clk) ((shift_dir == 1'b1) && (shift_amount == 2'b10)) |-> (out[15:12] == {A[1:0], 2'b00})
    );

    // A left shift by 3 keeps only A[0] in the MSB position.
    check_left_shift_by_3: assert property (
        @(posedge clk) ((shift_dir == 1'b1) && (shift_amount == 2'b11)) |-> (out[15:12] == {A[0], 3'b000})
    );

    // A right shift by 1 zero-fills the MSB.
    check_right_shift_by_1: assert property (
        @(posedge clk) ((shift_dir == 1'b0) && (shift_amount == 2'b01)) |-> (out[15:12] == {1'b0, A[3:1]})
    );

    // A right shift by 2 zero-fills the two MSBs.
    check_right_shift_by_2: assert property (
        @(posedge clk) ((shift_dir == 1'b0) && (shift_amount == 2'b10)) |-> (out[15:12] == {2'b00, A[3:2]})
    );

    // A right shift by 3 keeps only A[3] in the LSB position.
    check_right_shift_by_3: assert property (
        @(posedge clk) ((shift_dir == 1'b0) && (shift_amount == 2'b11)) |-> (out[15:12] == {3'b000, A[3]})
    );

    // The shifted upper nibble is stable when its driving inputs are stable.
    check_shift_nibble_stable_when_controls_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(shift_amount) && $stable(shift_dir)) |-> $stable(out[15:12])
    );

    // The shifted upper nibble only changes when A or shift controls change.
    check_shift_nibble_changes_only_with_controls: assert property (
        @(posedge clk) $changed(out[15:12]) |-> ($changed(A) || $changed(shift_amount) || $changed(shift_dir))
    );

endmodule