module shift_left_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic enable,
    input logic [7:0] data_out
);

    // When disabled, the output is driven to zero.
    check_disable_drives_zero: assert property (
        @(posedge clk) !enable |-> (data_out == 8'h00)
    );

    // When enabled, the output matches the implemented 8-bit left shift.
    check_enable_shifts_left_two: assert property (
        @(posedge clk) enable |-> (data_out == {data_in[5:0], 2'b00})
    );

    // When enabled, the two least-significant output bits are zero.
    check_enable_lsb_zero: assert property (
        @(posedge clk) enable |-> (data_out[1:0] == 2'b00)
    );

    // When enabled, output[7:2] reflects input[5:0].
    check_enable_upper_bits_map_input: assert property (
        @(posedge clk) enable |-> (data_out[7:2] == data_in[5:0])
    );

endmodule