module nand_decoder_sva (
    input logic clk,
    input logic [1:0] in,
    input logic [3:0] out
);

// out[0] is the inverse of the AND of in[0] and in[1].
    check_out0_inverts_and: assert property (
        @(posedge clk) out[0] == ~(in[0] & in[1])
    );

// out[1] is the inverse of the AND of in[0] and in[1].
    check_out1_inverts_and: assert property (
        @(posedge clk) out[1] == ~(in[0] & in[1])
    );

// out[2] is the inverse of the AND of in[0] and in[1].
    check_out2_inverts_and: assert property (
        @(posedge clk) out[2] == ~(in[0] & in[1])
    );

// out[3] is the inverse of the AND of in[0] and in[1].
    check_out3_inverts_and: assert property (
        @(posedge clk) out[3] == ~(in[0] & in[1])
    );

// When both inputs are HIGH, all outputs are LOW.
    check_all_low_when_both_high: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == 4'b0000)
    );

// When either input is LOW, all outputs are HIGH.
    check_all_high_when_any_low: assert property (
        @(posedge clk) (in != 2'b11) |-> (out == 4'b1111)
    );

endmodule
