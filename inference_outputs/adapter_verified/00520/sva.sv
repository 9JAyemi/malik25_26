module decoder_2to4_sva (
    input logic clk,
    input logic [1:0] in,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

// 00 decodes to out0=1, out1=0, out2=0, out3=0.
    check_decode_00: assert property (
        @(posedge clk) (in == 2'b00) |-> (out0 == 1'b1) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b0)
    );

// 01 decodes to out0=0, out1=1, out2=0, out3=0.
    check_decode_01: assert property (
        @(posedge clk) (in == 2'b01) |-> (out0 == 1'b0) && (out1 == 1'b1) && (out2 == 1'b0) && (out3 == 1'b0)
    );

// 10 decodes to out0=0, out1=0, out2=1, out3=0.
    check_decode_10: assert property (
        @(posedge clk) (in == 2'b10) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b1) && (out3 == 1'b0)
    );

// 11 decodes to out0=0, out1=0, out2=0, out3=1.
    check_decode_11: assert property (
        @(posedge clk) (in == 2'b11) |-> (out0 == 1'b0) && (out1 == 1'b0) && (out2 == 1'b0) && (out3 == 1'b1)
    );

// Exactly one output is asserted for all input values.
    check_onehot_output: assert property (
        @(posedge clk) $onehot({out0, out1, out2, out3})
    );

// Output bits are never asserted in combination.
    check_output_mutex: assert property (
        @(posedge clk) !(out0 && out1) && !(out0 && out2) && !(out0 && out3) && !(out1 && out2) && !(out1 && out3) && !(out2 && out3)
    );

endmodule
