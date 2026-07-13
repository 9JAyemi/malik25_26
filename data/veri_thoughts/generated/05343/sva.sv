module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] ctrl,
    input logic [3:0] out
);

    // Output matches the selected shift operation for all control values.
    check_functional_mapping: assert property (
        @(posedge clk)
        out == ((ctrl == 2'b00) ? {in[2:0], 1'b0} :
                (ctrl == 2'b01) ? {in[1:0], 2'b00} :
                (ctrl == 2'b10) ? {1'b0, in[3:1]} :
                                  {2'b00, in[3:2]})
    );

    // ctrl 00 shifts left by 1 with zero fill.
    check_ctrl_00_shift_left_1: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (out == {in[2:0], 1'b0})
    );

    // ctrl 01 shifts left by 2 with zero fill.
    check_ctrl_01_shift_left_2: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (out == {in[1:0], 2'b00})
    );

    // ctrl 10 shifts right by 1 with zero fill.
    check_ctrl_10_shift_right_1: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (out == {1'b0, in[3:1]})
    );

    // ctrl 11 shifts right by 2 with zero fill.
    check_ctrl_11_shift_right_2: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (out == {2'b00, in[3:2]})
    );

endmodule