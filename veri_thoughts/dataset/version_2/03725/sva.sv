module sign_inverter_sva #(parameter W = 32) (
    input logic clk,
    input logic [W-1:0] data,
    input logic [1:0] shift_region_flag,
    input logic operation,
    input logic [W-1:0] data_out
);

    // DUT is combinational with no native clock or reset; clk samples assertions.
    localparam [W-1:0] SIGN_TOGGLE_MASK = ({W{1'b1}} << (W-1));

    // Flags 00 and 11 always pass the input through.
    check_common_regions_passthrough: assert property (
        @(posedge clk)
        ((shift_region_flag == 2'b00) || (shift_region_flag == 2'b11)) |-> (data_out == data)
    );

    // With operation low and region 01, only the sign bit is inverted.
    check_op0_region01_inverts_sign: assert property (
        @(posedge clk)
        ((operation == 1'b0) && (shift_region_flag == 2'b01)) |-> (data_out == (data ^ SIGN_TOGGLE_MASK))
    );

    // With operation low and region 10, the output matches the input.
    check_op0_region10_passthrough: assert property (
        @(posedge clk)
        ((operation == 1'b0) && (shift_region_flag == 2'b10)) |-> (data_out == data)
    );

    // With operation high and region 10, only the sign bit is inverted.
    check_op1_region10_inverts_sign: assert property (
        @(posedge clk)
        ((operation == 1'b1) && (shift_region_flag == 2'b10)) |-> (data_out == (data ^ SIGN_TOGGLE_MASK))
    );

    // With operation high and region 01, the output matches the input.
    check_op1_region01_passthrough: assert property (
        @(posedge clk)
        ((operation == 1'b1) && (shift_region_flag == 2'b01)) |-> (data_out == data)
    );

    // Any output difference from the input is a sign-bit-only change.
    check_only_sign_bit_can_change: assert property (
        @(posedge clk)
        (data_out != data) |-> ((data_out ^ data) == SIGN_TOGGLE_MASK)
    );

    // Output differs from input only in the two active inversion cases.
    check_difference_only_in_active_cases: assert property (
        @(posedge clk)
        (data_out != data) |-> (((operation == 1'b0) && (shift_region_flag == 2'b01)) ||
                                ((operation == 1'b1) && (shift_region_flag == 2'b10)))
    );

    // Complete combinational mapping from inputs to output.
    check_complete_mapping: assert property (
        @(posedge clk)
        data_out == ((((operation == 1'b0) && (shift_region_flag == 2'b01)) ||
                      ((operation == 1'b1) && (shift_region_flag == 2'b10)))
                     ? (data ^ SIGN_TOGGLE_MASK) : data)
    );

endmodule