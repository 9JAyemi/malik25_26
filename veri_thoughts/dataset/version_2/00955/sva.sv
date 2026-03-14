module barrel_shifter_sva (
    input logic CLK,
    input logic [7:0] in,
    input logic [2:0] shift_amount,
    input logic direction,
    input logic [7:0] out
);
    // Left shift selected: out equals in << shift_amount.
    check_left_shift_result: assert property (
        @(posedge CLK) (direction == 1'b0) |-> (out == (in << shift_amount))
    );

    // Right shift selected: out equals in >> shift_amount.
    check_right_shift_result: assert property (
        @(posedge CLK) (direction == 1'b1) |-> (out == (in >> shift_amount))
    );

    // Zero shift amount passes input through regardless of direction.
    check_shift_zero_passthrough: assert property (
        @(posedge CLK) (shift_amount == 3'd0) |-> (out == in)
    );

    // Left shift with nonzero amount zero-fills LSB.
    check_left_shift_lsb_zero_when_nonzero: assert property (
        @(posedge CLK) ((direction == 1'b0) && (shift_amount != 3'd0)) |-> (out[0] == 1'b0)
    );

    // Right shift with nonzero amount zero-fills MSB.
    check_right_shift_msb_zero_when_nonzero: assert property (
        @(posedge CLK) ((direction == 1'b1) && (shift_amount != 3'd0)) |-> (out[7] == 1'b0)
    );

    // Extreme case: left shift by 7 places.
    check_extreme_left_shift7: assert property (
        @(posedge CLK) ((direction == 1'b0) && (shift_amount == 3'd7)) |-> (out == {in[0], 7'b0})
    );

    // Extreme case: right shift by 7 places.
    check_extreme_right_shift7: assert property (
        @(posedge CLK) ((direction == 1'b1) && (shift_amount == 3'd7)) |-> (out == {7'b0, in[7]})
    );

    // Specific case: left shift by 1 place.
    check_left_shift1_pattern: assert property (
        @(posedge CLK) ((direction == 1'b0) && (shift_amount == 3'd1)) |-> (out == {in[6:0], 1'b0})
    );

    // Zero input always yields zero output.
    check_zero_input_yields_zero_output: assert property (
        @(posedge CLK) (in == 8'b0) |-> (out == 8'b0)
    );

    // If inputs are stable, output remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable(in) && $stable(shift_amount) && $stable(direction) |-> $stable(out)
    );
endmodule