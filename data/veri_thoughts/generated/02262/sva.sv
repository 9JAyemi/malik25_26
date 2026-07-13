module four_bit_decoder_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // Out is always a known 2-bit value.
    check_out_known: assert property (
        @(posedge clk) disable iff (1'b0) !$isunknown(out)
    );

    // Inputs 0..4 map to 00.
    check_map_00_forward: assert property (
        @(posedge clk) disable iff (1'b0) (in inside {[4'd0:4'd4]}) |-> (out == 2'b00)
    );

    // Inputs 5..8 map to 01.
    check_map_01_forward: assert property (
        @(posedge clk) disable iff (1'b0) (in inside {[4'd5:4'd8]}) |-> (out == 2'b01)
    );

    // Inputs 9..11 map to 10.
    check_map_10_forward: assert property (
        @(posedge clk) disable iff (1'b0) (in inside {[4'd9:4'd11]}) |-> (out == 2'b10)
    );

    // Inputs 12..15 map to 11.
    check_map_11_forward: assert property (
        @(posedge clk) disable iff (1'b0) (in inside {[4'd12:4'd15]}) |-> (out == 2'b11)
    );

    // Out 00 only occurs for inputs 0..4.
    check_map_00_reverse: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b00) |-> (in inside {[4'd0:4'd4]})
    );

    // Out 01 only occurs for inputs 5..8.
    check_map_01_reverse: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b01) |-> (in inside {[4'd5:4'd8]})
    );

    // Out 10 only occurs for inputs 9..11.
    check_map_10_reverse: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b10) |-> (in inside {[4'd9:4'd11]})
    );

    // Out 11 only occurs for inputs 12..15.
    check_map_11_reverse: assert property (
        @(posedge clk) disable iff (1'b0) (out == 2'b11) |-> (in inside {[4'd12:4'd15]})
    );

    // If input is stable, output is stable (purely combinational function).
    check_stability_with_stable_input: assert property (
        @(posedge clk) disable iff (1'b0) $stable(in) |-> $stable(out)
    );

endmodule