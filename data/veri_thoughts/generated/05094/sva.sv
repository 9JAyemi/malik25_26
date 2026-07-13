module barrel_shifter_sva(
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] shift_amt,
    input logic [3:0] data_out
);

    // Shift amount 0 passes the input through unchanged.
    check_no_shift_passthrough: assert property (
        @(posedge clk) (shift_amt == 2'b00) |-> (data_out == data_in)
    );

    // Shift amount 1 shifts left by one and inserts 0 in bit 0.
    check_shift_by_one: assert property (
        @(posedge clk) (shift_amt == 2'b01) |-> (data_out == {data_in[2:0], 1'b0})
    );

    // Shift amount 2 shifts left by two and inserts 0s in bits [1:0].
    check_shift_by_two: assert property (
        @(posedge clk) (shift_amt == 2'b10) |-> (data_out == {data_in[1:0], 2'b00})
    );

    // Shift amount 3 shifts left by three and inserts 0s in bits [2:0].
    check_shift_by_three: assert property (
        @(posedge clk) (shift_amt == 2'b11) |-> (data_out == {data_in[0], 3'b000})
    );

endmodule