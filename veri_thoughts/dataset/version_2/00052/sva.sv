module decoder_2to4_sva (
    input logic clk,
    input logic [1:0] in,
    input logic [3:0] out
);

    // Full output matches the implemented NAND-based logic.
    check_output_equation: assert property (
        @(posedge clk) out == {1'b0, (in[0] & in[1]), (in[0] & ~in[1]), ~in[0]}
    );

    // The MSB of out is never asserted by this implementation.
    check_out3_constant_low: assert property (
        @(posedge clk) out[3] == 1'b0
    );

    // out[2] is asserted only when both input bits are high.
    check_out2_equation: assert property (
        @(posedge clk) out[2] == (in[0] & in[1])
    );

    // out[1] is asserted only when in is 2'b01.
    check_out1_equation: assert property (
        @(posedge clk) out[1] == (in[0] & ~in[1])
    );

    // out[0] is asserted whenever in[0] is low.
    check_out0_equation: assert property (
        @(posedge clk) out[0] == ~in[0]
    );

    // Exactly one output bit is high for every input combination.
    check_output_onehot: assert property (
        @(posedge clk) $onehot(out)
    );

    // Any input with in[0] low maps to 4'b0001.
    check_low_in0_case: assert property (
        @(posedge clk) (!in[0]) |-> (out == 4'b0001)
    );

    // Input 2'b01 maps to 4'b0010.
    check_input_01_case: assert property (
        @(posedge clk) (in == 2'b01) |-> (out == 4'b0010)
    );

    // Input 2'b11 maps to 4'b0100.
    check_input_11_case: assert property (
        @(posedge clk) (in == 2'b11) |-> (out == 4'b0100)
    );

endmodule