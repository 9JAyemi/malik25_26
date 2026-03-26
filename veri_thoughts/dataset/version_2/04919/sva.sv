module data_control_sva (
    input logic clk,
    input logic [15:0] data_in,
    input logic [3:0]  control_in,
    input logic [15:0] data_out,
    input logic [3:0]  control_out
);

    // data_out always matches data_in incremented by one.
    check_data_increment: assert property (
        @(posedge clk) data_out == (data_in + 16'd1)
    );

    // data_out wraps to zero when data_in is all ones.
    check_data_wraparound: assert property (
        @(posedge clk) (data_in == 16'hFFFF) |-> (data_out == 16'h0000)
    );

    // Incrementing by one always toggles the least-significant bit.
    check_data_lsb_toggle: assert property (
        @(posedge clk) data_out[0] == ~data_in[0]
    );

    // control_out always matches control_in shifted left by one.
    check_control_shift: assert property (
        @(posedge clk) control_out == (control_in << 1)
    );

    // A left shift by one always drives the low bit to zero.
    check_control_lsb_zero: assert property (
        @(posedge clk) control_out[0] == 1'b0
    );

    // Shifted control bits map to the next higher positions.
    check_control_shifted_bits: assert property (
        @(posedge clk) control_out[3:1] == control_in[2:0]
    );

endmodule