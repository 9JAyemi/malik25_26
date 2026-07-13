module signal_modifier_sva (
    input  logic        CLK,   // verification clock (DUT has no clock/reset)
    input  logic [15:0] in,
    input  logic [1:0]  ctrl,
    input  logic [15:0] out
);

    ///// Functional correctness /////
    // When ctrl==00, out equals in.
    check_ctrl_00_passthrough: assert property (
        @(posedge CLK) (ctrl == 2'b00) |-> (out == in)
    );

    // When ctrl==01, out equals bitwise NOT of in.
    check_ctrl_01_invert: assert property (
        @(posedge CLK) (ctrl == 2'b01) |-> (out == ~in)
    );

    // When ctrl==10, out equals in shifted left by 2 with zeros in LSBs.
    check_ctrl_10_shift_left2: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (out == {in[13:0], 2'b00})
    );

    // When ctrl==11, out equals in shifted right by 2 with zeros in MSBs.
    check_ctrl_11_shift_right2: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (out == {2'b00, in[15:2]})
    );

    // Out matches the selected transformation for all ctrl values.
    check_functional_mapping: assert property (
        @(posedge CLK)
            out ==
                ((ctrl == 2'b00) ? in :
                 (ctrl == 2'b01) ? ~in :
                 (ctrl == 2'b10) ? {in[13:0], 2'b00} :
                                   {2'b00, in[15:2]})
    );

    ///// Bit-level implications /////
    // For shift-left (10), LSBs of out are zero.
    check_shift_left2_lsb_zero: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (out[1:0] == 2'b00)
    );

    // For shift-right (11), MSBs of out are zero.
    check_shift_right2_msb_zero: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (out[15:14] == 2'b00)
    );

    // For shift-left (10), out[15:2] equals in[13:0].
    check_shift_left2_upper_bits: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (out[15:2] == in[13:0])
    );

    // For shift-right (11), out[13:0] equals in[15:2].
    check_shift_right2_lower_bits: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (out[13:0] == in[15:2])
    );

    ///// Stability /////
    // If in and ctrl are stable across a cycle, out must be stable.
    check_stability: assert property (
        @(posedge CLK) $stable({in, ctrl}) |-> $stable(out)
    );

endmodule