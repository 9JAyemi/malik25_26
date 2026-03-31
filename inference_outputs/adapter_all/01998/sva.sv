module priority_encoder_sva #(
    parameter int n = 4,
    parameter int m = 2
) (
    input logic clk,
    input logic [n-1:0] in,
    input logic [m-1:0] out
);

    // Priority 0001 maps to 00.
    check_priority_0001_maps_to_00: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b0001) |-> (out == 2'b00)
    );

    // Priority 0010 maps to 01.
    check_priority_0010_maps_to_01: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b0010) |-> (out == 2'b01)
    );

    // Priority 0100 maps to 10.
    check_priority_0100_maps_to_10: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b0100) |-> (out == 2'b10)
    );

    // Priority 1000 maps to 11.
    check_priority_1000_maps_to_11: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b1000) |-> (out == 2'b11)
    );

    // Any other input pattern maps to the default 00.
    check_default_maps_to_00: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in != 4'b0001) && (in != 4'b0010) && (in != 4'b0100) && (in != 4'b1000)) |-> (out == 2'b00)
    );

    // Output 01 can only come from priority 0010.
    check_out_01_only_from_priority_0010: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 2'b01) |-> (in == 4'b0010)
    );

    // Output 10 can only come from priority 0100.
    check_out_10_only_from_priority_0100: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 2'b10) |-> (in == 4'b0100)
    );

    // Output 11 can only come from priority 1000.
    check_out_11_only_from_priority_1000: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 2'b11) |-> (in == 4'b1000)
    );

    // Output 00 can come from any non-winning input pattern.
    check_out_00_from_nonwinning_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
        ((in != 4'b0001) && (in != 4'b0010) && (in != 4'b0100) && (in != 4'b1000)) |-> (out == 2'b00)
    );

    // Output 00 can also come from the highest-priority input pattern 1110.
    check_out_00_from_priority_1110: assert property (
        @(posedge clk) disable iff (1'b0)
        (in == 4'b1110) |-> (out == 2'b00)
    );

endmodule