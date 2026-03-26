module data_ctrl_sva(
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] ctrl,
    input logic [3:0] data_out
);

    // Output is zero when ctrl selects 2'b00.
    check_ctrl_zero_output_zero: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (data_out == 4'b0000)
    );

    // Output is all ones when ctrl selects 2'b01.
    check_ctrl_one_output_ones: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (data_out == 4'b1111)
    );

    // Output passes data_in through when ctrl selects 2'b10.
    check_ctrl_two_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (data_out == data_in)
    );

    // Output is inverted data_in when ctrl selects 2'b11.
    check_ctrl_three_invert: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (data_out == ~data_in)
    );

    // Output always matches the RTL mux expression.
    check_full_output_mapping: assert property (
        @(posedge clk)
        data_out == ((ctrl == 2'b00) ? 4'b0000 :
                     (ctrl == 2'b01) ? 4'b1111 :
                     (ctrl == 2'b10) ? data_in :
                                       ~data_in)
    );

endmodule