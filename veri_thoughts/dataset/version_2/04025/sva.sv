module priority_encoder_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] in,
    input logic [1:0] out
);

    // Reset forces the registered output to 00.
    check_reset_drives_out_zero: assert property (
        @(posedge clk) rst |=> (out == 2'b00)
    );

    // Input 0001 updates the output to 00 on the next clock.
    check_input_0001_maps_to_00: assert property (
        @(posedge clk) disable iff (rst)
        (in == 4'b0001) |=> (out == 2'b00)
    );

    // Input 0010 updates the output to 01 on the next clock.
    check_input_0010_maps_to_01: assert property (
        @(posedge clk) disable iff (rst)
        (in == 4'b0010) |=> (out == 2'b01)
    );

    // Input 0100 updates the output to 10 on the next clock.
    check_input_0100_maps_to_10: assert property (
        @(posedge clk) disable iff (rst)
        (in == 4'b0100) |=> (out == 2'b10)
    );

    // Input 1000 updates the output to 11 on the next clock.
    check_input_1000_maps_to_11: assert property (
        @(posedge clk) disable iff (rst)
        (in == 4'b1000) |=> (out == 2'b11)
    );

    // Any other input pattern updates the output to 00 on the next clock.
    check_all_other_inputs_map_to_00: assert property (
        @(posedge clk) disable iff (rst)
        ((in != 4'b0001) && (in != 4'b0010) && (in != 4'b0100) && (in != 4'b1000)) |=> (out == 2'b00)
    );

endmodule