module signal_converter_sva (
    input logic clk,
    input logic [3:0] in_signal,
    input logic [2:0] out_signal
);

    // For in_signal < 4, out_signal equals in_signal.
    check_map_lt4: assert property (
        @(posedge clk) (in_signal < 4'd4) |-> (out_signal == in_signal[2:0])
    );

    // For 4 <= in_signal < 8, out_signal equals in_signal - 1.
    check_map_4_to_7: assert property (
        @(posedge clk) ((in_signal >= 4'd4) && (in_signal < 4'd8)) |-> (out_signal == (in_signal - 4'd1)[2:0])
    );

    // For in_signal >= 8, out_signal equals in_signal - 2 (truncated to 3 bits).
    check_map_ge8: assert property (
        @(posedge clk) (in_signal >= 4'd8) |-> (out_signal == (in_signal - 4'd2)[2:0])
    );

    // Boundary: in_signal == 0 => out_signal == 0.
    check_in0: assert property (
        @(posedge clk) (in_signal == 4'd0) |-> (out_signal == 3'd0)
    );

    // Boundary: in_signal == 3 => out_signal == 3.
    check_in3: assert property (
        @(posedge clk) (in_signal == 4'd3) |-> (out_signal == 3'd3)
    );

    // Boundary: in_signal == 4 => out_signal == 3 (start of middle range).
    check_in4: assert property (
        @(posedge clk) (in_signal == 4'd4) |-> (out_signal == 3'd3)
    );

    // Boundary: in_signal == 7 => out_signal == 6 (end of middle range).
    check_in7: assert property (
        @(posedge clk) (in_signal == 4'd7) |-> (out_signal == 3'd6)
    );

    // Boundary: in_signal == 8 => out_signal == 6 (start of upper range).
    check_in8: assert property (
        @(posedge clk) (in_signal == 4'd8) |-> (out_signal == 3'd6)
    );

    // Wrap example: in_signal == 10 => out_signal == 0 ((10-2)=8 -> 3'b000).
    check_in10_wrap0: assert property (
        @(posedge clk) (in_signal == 4'd10) |-> (out_signal == 3'd0)
    );

    // Boundary: in_signal == 15 => out_signal == 5 ((15-2)=13 -> 3'b101).
    check_in15: assert property (
        @(posedge clk) (in_signal == 4'd15) |-> (out_signal == 3'd5)
    );

endmodule