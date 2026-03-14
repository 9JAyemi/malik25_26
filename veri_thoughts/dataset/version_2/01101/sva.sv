module signal_converter_sva (
    input logic CLK,
    input logic [3:0] in_signal,
    input logic [1:0] out_signal
);
    // in_signal 0..3 must map to 2'b00
    check_map_0_to_3_is_00: assert property (
        @(posedge CLK) (in_signal inside {[4'd0:4'd3]}) |-> (out_signal == 2'b00)
    );

    // in_signal 4..7 must map to 2'b01
    check_map_4_to_7_is_01: assert property (
        @(posedge CLK) (in_signal inside {[4'd4:4'd7]}) |-> (out_signal == 2'b01)
    );

    // in_signal 8..10 must map to 2'b10
    check_map_8_to_10_is_10: assert property (
        @(posedge CLK) (in_signal inside {[4'd8:4'd10]}) |-> (out_signal == 2'b10)
    );

    // in_signal 11..15 must map to 2'b11 (default)
    check_map_11_to_15_is_11: assert property (
        @(posedge CLK) (in_signal inside {[4'd11:4'd15]}) |-> (out_signal == 2'b11)
    );

    // 2'b00 output implies in_signal is 0..3
    check_rev_00_implies_0_to_3: assert property (
        @(posedge CLK) (out_signal == 2'b00) |-> (in_signal inside {[4'd0:4'd3]})
    );

    // 2'b01 output implies in_signal is 4..7
    check_rev_01_implies_4_to_7: assert property (
        @(posedge CLK) (out_signal == 2'b01) |-> (in_signal inside {[4'd4:4'd7]})
    );

    // 2'b10 output implies in_signal is 8..10
    check_rev_10_implies_8_to_10: assert property (
        @(posedge CLK) (out_signal == 2'b10) |-> (in_signal inside {[4'd8:4'd10]})
    );

    // 2'b11 output implies in_signal is 11..15
    check_rev_11_implies_11_to_15: assert property (
        @(posedge CLK) (out_signal == 2'b11) |-> (in_signal inside {[4'd11:4'd15]})
    );
endmodule