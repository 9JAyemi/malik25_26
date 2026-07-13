module consecutive_ones_sva (
    input logic clk,
    input logic [3:0] in_signal,
    input logic [1:0] out_signal
);

    // out_signal is 00 when the lower three input bits are 000.
    check_out_zero_for_low3_000: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b000) |-> (out_signal == 2'b00)
    );

    // out_signal is 01 when the lower three input bits are 001.
    check_out_one_for_low3_001: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b001) |-> (out_signal == 2'b01)
    );

    // out_signal is 01 when the lower three input bits are 010.
    check_out_one_for_low3_010: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b010) |-> (out_signal == 2'b01)
    );

    // out_signal is 01 when the lower three input bits are 011.
    check_out_one_for_low3_011: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b011) |-> (out_signal == 2'b01)
    );

    // out_signal is 01 when the lower three input bits are 100.
    check_out_one_for_low3_100: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b100) |-> (out_signal == 2'b01)
    );

    // out_signal is 10 when the lower three input bits are 101.
    check_out_two_for_low3_101: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b101) |-> (out_signal == 2'b10)
    );

    // out_signal is 10 when the lower three input bits are 110.
    check_out_two_for_low3_110: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b110) |-> (out_signal == 2'b10)
    );

    // out_signal is 10 when the lower three input bits are 111.
    check_out_two_for_low3_111: assert property (
        @(posedge clk) (in_signal[2:0] == 3'b111) |-> (out_signal == 2'b10)
    );

    // out_signal is 00 only for the lower-three-bits value 000.
    check_out_zero_only_for_low3_000: assert property (
        @(posedge clk) (out_signal == 2'b00) |-> (in_signal[2:0] == 3'b000)
    );

    // out_signal never takes the unused value 11.
    check_out_never_11: assert property (
        @(posedge clk) (out_signal != 2'b11)
    );

endmodule