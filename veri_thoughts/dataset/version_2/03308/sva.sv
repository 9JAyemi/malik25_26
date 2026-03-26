module Convolutional_Encoder_Viterbi_Decoder_assertions #(
    parameter int k = 3,
    parameter int n = 4,
    parameter int m = 3
) (
    input logic [n-1:0] in,
    input logic [m-1:0] out,
    input logic clk
);

    // Out holds the lower m input bits sampled on the previous clock.
    check_out_matches_prior_input: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (out == $past(in[m-1:0]))
    );

    // A sampled 000 value appears on out on the next clock.
    check_decode_000: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b000) |=> (out == 3'b000)
    );

    // A sampled 001 value appears on out on the next clock.
    check_decode_001: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b001) |=> (out == 3'b001)
    );

    // A sampled 010 value appears on out on the next clock.
    check_decode_010: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b010) |=> (out == 3'b010)
    );

    // A sampled 011 value appears on out on the next clock.
    check_decode_011: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b011) |=> (out == 3'b011)
    );

    // A sampled 100 value appears on out on the next clock.
    check_decode_100: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b100) |=> (out == 3'b100)
    );

    // A sampled 101 value appears on out on the next clock.
    check_decode_101: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b101) |=> (out == 3'b101)
    );

    // A sampled 110 value appears on out on the next clock.
    check_decode_110: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b110) |=> (out == 3'b110)
    );

    // A sampled 111 value appears on out on the next clock.
    check_decode_111: assert property (
        @(posedge clk) disable iff (1'b0)
        (in[m-1:0] == 3'b111) |=> (out == 3'b111)
    );

endmodule