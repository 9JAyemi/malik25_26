module lcd_driver_sva (
    input logic [3:0] data,
    input logic [1:0] ctrl,
    input logic [6:0] seg
);

    // Lower nibble matches the implemented data/control equation.
    check_seg_lower_nibble_function: assert property (
        @($global_clock)
        seg[3:0] == ((data & {4{ctrl[0]}}) | ((~data) & {4{ctrl[1]}}))
    );

    // seg[4] is driven directly by ctrl[0].
    check_seg4_matches_ctrl0: assert property (
        @($global_clock)
        seg[4] == ctrl[0]
    );

    // seg[5] is driven directly by ctrl[1].
    check_seg5_matches_ctrl1: assert property (
        @($global_clock)
        seg[5] == ctrl[1]
    );

    // seg[6] is always tied low.
    check_seg6_tied_low: assert property (
        @($global_clock)
        seg[6] == 1'b0
    );

    // ctrl=00 forces the lower nibble to zero.
    check_ctrl_00_lower_nibble_zero: assert property (
        @($global_clock)
        (ctrl == 2'b00) |-> (seg[3:0] == 4'b0000)
    );

    // ctrl=01 passes data to the lower nibble.
    check_ctrl_01_lower_nibble_data: assert property (
        @($global_clock)
        (ctrl == 2'b01) |-> (seg[3:0] == data)
    );

    // ctrl=10 inverts data onto the lower nibble.
    check_ctrl_10_lower_nibble_inverted_data: assert property (
        @($global_clock)
        (ctrl == 2'b10) |-> (seg[3:0] == ~data)
    );

    // ctrl=11 forces the lower nibble high.
    check_ctrl_11_lower_nibble_ones: assert property (
        @($global_clock)
        (ctrl == 2'b11) |-> (seg[3:0] == 4'b1111)
    );

endmodule