module barrel_shifter_sva (
    input logic CLK,
    input logic [15:0] in,
    input logic [3:0] shift,
    input logic [15:0] out
);
    ///// Functional mapping to left shift /////
    // For known shift, out equals in left-shifted by shift.
    check_out_eq_left_shift_when_shift_known: assert property (
        @(posedge CLK) (!$isunknown(shift)) |-> (out == (in << shift))
    );

    // Zero shift passes input through unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge CLK) (shift == 4'd0) |-> (out == in)
    );

    // One-bit shift produces {in[14:0], 1'b0}.
    check_one_shift_behavior: assert property (
        @(posedge CLK) (shift == 4'd1) |-> (out == {in[14:0], 1'b0})
    );

    // Max shift (15) produces {in[0], 15'b0}.
    check_max_shift_behavior: assert property (
        @(posedge CLK) (shift == 4'd15) |-> (out == {in[0], 15'b0})
    );

    ///// Structural bit properties of left shift /////
    // For known positive shift, LSBs are zero-filled.
    check_lsb_zero_fill_mask: assert property (
        @(posedge CLK) (!$isunknown(shift) && (shift > 4'd0)) |-> ((out & ((16'h0001 << shift) - 16'h0001)) == 16'h0000)
    );

    // For known shift, right-shifting out by shift restores masked in.
    check_out_right_shift_mask_relation: assert property (
        @(posedge CLK) (!$isunknown(shift)) |-> ((out >> shift) == (in & (16'hFFFF >> shift)))
    );

    // For known shift, MSB of out equals in[15 - shift].
    check_msb_maps_from_in: assert property (
        @(posedge CLK) (!$isunknown(shift)) |-> (out[15] == in[15 - shift])
    );

    // For known positive shift, LSB is 0.
    check_lsb_zero_when_shift_pos: assert property (
        @(posedge CLK) (!$isunknown(shift) && (shift > 4'd0)) |-> (out[0] == 1'b0)
    );

    ///// Stability /////
    // If inputs are stable, output remains stable.
    check_output_stability_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(in) && $stable(shift)) |-> $stable(out)
    );

    ///// Per-bit movement (only when destination index is in range) /////
    // For known shift, a '1' at in[i] moves to out[i+shift] if i+shift <= 15.
    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : gen_move_bits
            check_bit_move: assert property (
                @(posedge CLK) (!$isunknown(shift) && (in[i] === 1'b1) && ((i + shift) <= 4'd15)) |-> (out[i + shift] === 1'b1)
            );
        end
    endgenerate
endmodule