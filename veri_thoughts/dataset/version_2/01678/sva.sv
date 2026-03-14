module divider_sva (
    input logic CLK,
    input logic [3:0] data_in,
    input logic [1:0] data_out
);
    // Analysis: No clock or reset in RTL; pure combinational always @*. Assertions are sampled on external CLK.
    // Analysis: Maps data_in 0-2->00, 3-5->01, 6-8->10, 9-11->11; 12-15 hit default->00.

    // 0..2 must map to 2'b00.
    map_0_to_2_is_00: assert property (
        @(posedge CLK) (data_in inside {4'd0,4'd1,4'd2}) |-> (data_out == 2'b00)
    );

    // 3..5 must map to 2'b01.
    map_3_to_5_is_01: assert property (
        @(posedge CLK) (data_in inside {4'd3,4'd4,4'd5}) |-> (data_out == 2'b01)
    );

    // 6..8 must map to 2'b10.
    map_6_to_8_is_10: assert property (
        @(posedge CLK) (data_in inside {4'd6,4'd7,4'd8}) |-> (data_out == 2'b10)
    );

    // 9..11 must map to 2'b11.
    map_9_to_11_is_11: assert property (
        @(posedge CLK) (data_in inside {4'd9,4'd10,4'd11}) |-> (data_out == 2'b11)
    );

    // 12..15 hit default and must map to 2'b00.
    map_12_to_15_default_is_00: assert property (
        @(posedge CLK) (data_in >= 4'd12) |-> (data_out == 2'b00)
    );

    // If output is 2'b00, input must be 0..2 or 12..15.
    reverse_00_inputs: assert property (
        @(posedge CLK) (data_out == 2'b00) |-> (data_in inside {4'd0,4'd1,4'd2,4'd12,4'd13,4'd14,4'd15})
    );

    // If output is 2'b01, input must be 3..5.
    reverse_01_inputs: assert property (
        @(posedge CLK) (data_out == 2'b01) |-> (data_in inside {4'd3,4'd4,4'd5})
    );

    // If output is 2'b10, input must be 6..8.
    reverse_10_inputs: assert property (
        @(posedge CLK) (data_out == 2'b10) |-> (data_in inside {4'd6,4'd7,4'd8})
    );

    // If output is 2'b11, input must be 9..11.
    reverse_11_inputs: assert property (
        @(posedge CLK) (data_out == 2'b11) |-> (data_in inside {4'd9,4'd10,4'd11})
    );

endmodule