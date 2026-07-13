module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift,
    input logic [3:0] out
);

    // Shift 00 passes the input through unchanged.
    check_pass_through: assert property (
        @(posedge clk) (shift == 2'b00) |-> (out == data_in)
    );

    // Shift 01 performs a left shift by 1 with zero fill.
    check_shift_left_by_1: assert property (
        @(posedge clk) (shift == 2'b01) |-> (out == {data_in[2:0], 1'b0})
    );

    // Shift 10 performs a right shift by 1 with zero fill.
    check_shift_right_by_1: assert property (
        @(posedge clk) (shift == 2'b10) |-> (out == {1'b0, data_in[3:1]})
    );

    // Shift 11 performs a left shift by 2 with zero fill.
    check_shift_left_by_2: assert property (
        @(posedge clk) (shift == 2'b11) |-> (out == {data_in[1:0], 2'b00})
    );

    // Output always matches the selected shift operation.
    check_functional_mapping: assert property (
        @(posedge clk)
        (out == ((shift == 2'b00) ? data_in :
                 (shift == 2'b01) ? {data_in[2:0], 1'b0} :
                 (shift == 2'b10) ? {1'b0, data_in[3:1]} :
                                    {data_in[1:0], 2'b00}))
    );

endmodule