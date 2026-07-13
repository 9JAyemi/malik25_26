module barrel_shifter_sva (
    input logic clk,                // Sampling clock for SVA (RTL has no clock/reset)
    input logic [3:0] data,
    input logic shift_left,
    input logic shift_right,
    input logic rotate_right,
    input logic [3:0] shifted_data
);
    ///// Functional equivalence checks /////
    // When shift_right=1, output is right shift of stage1_data (priority over rotate_right).
    check_shift_right_full: assert property (
        @(posedge clk)
        shift_right |-> (shifted_data == {1'b0,
                                          (shift_left ? data[2] : 1'b0),
                                          (shift_left ? data[1] : data[3]),
                                          (shift_left ? data[0] : data[2])})
    );

    // When !shift_right && rotate_right=1, output is rotate-right of stage1_data.
    check_rotate_right_full: assert property (
        @(posedge clk)
        (!shift_right && rotate_right) |-> (shifted_data == {(shift_left ? 1'b0 : data[1]),
                                                            (shift_left ? data[2] : 1'b0),
                                                            (shift_left ? data[1] : data[3]),
                                                            (shift_left ? data[0] : data[2])})
    );

    // When !shift_right && !rotate_right, output passes stage1_data.
    check_passthrough_full: assert property (
        @(posedge clk)
        (!shift_right && !rotate_right) |-> (shifted_data == (shift_left ? {data[2:0], 1'b0}
                                                                        : {1'b0, data[3:1]}))
    );

    ///// Bit-level invariants /////
    // In shift_right path, MSB is zero-filled.
    check_shift_right_msb_zero: assert property (
        @(posedge clk)
        shift_right |-> (shifted_data[3] == 1'b0)
    );

    // In rotate_right path, MSB comes from stage1_data[0].
    check_rotate_right_msb_mapping: assert property (
        @(posedge clk)
        (!shift_right && rotate_right) |-> (shifted_data[3] == (shift_left ? 1'b0 : data[1]))
    );

    // In passthrough path, LSB equals stage1_data[0].
    check_passthrough_lsb_mapping: assert property (
        @(posedge clk)
        (!shift_right && !rotate_right) |-> (shifted_data[0] == (shift_left ? 1'b0 : data[1]))
    );

    // In rotate_right path, LSB equals stage1_data[1].
    check_rotate_right_lsb_mapping: assert property (
        @(posedge clk)
        (!shift_right && rotate_right) |-> (shifted_data[0] == (shift_left ? data[0] : data[2]))
    );

    // In passthrough path, MSB equals stage1_data[3].
    check_passthrough_msb_mapping: assert property (
        @(posedge clk)
        (!shift_right && !rotate_right) |-> (shifted_data[3] == (shift_left ? data[2] : 1'b0))
    );

    // In shift_right path, bit[1] maps from stage1_data[2].
    check_shift_right_bit1_mapping: assert property (
        @(posedge clk)
        shift_right |-> (shifted_data[1] == (shift_left ? data[1] : data[3]))
    );

    // In rotate_right path, bit[2] maps from stage1_data[2].
    check_rotate_right_bit2_mapping: assert property (
        @(posedge clk)
        (!shift_right && rotate_right) |-> (shifted_data[2] == (shift_left ? data[1] : data[3]))
    );

    ///// Priority/independence /////
    // With shift_right held high and other used inputs stable, output is independent of rotate_right.
    check_shift_right_independent_of_rotate: assert property (
        @(posedge clk)
        (shift_right && $stable({data, shift_left, shift_right})) |-> $stable(shifted_data)
    );
endmodule