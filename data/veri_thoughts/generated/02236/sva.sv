module gray_code_converter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] gray_out
);
    // gray_out[0] equals in[0].
    check_gray0_is_in0: assert property (
        @(posedge clk) gray_out[0] == in[0]
    );

    // gray_out[1] equals in[0] XOR in[1].
    check_gray1_is_in0_xor_in1: assert property (
        @(posedge clk) gray_out[1] == (in[0] ^ in[1])
    );

    // gray_out[2] equals in[1] XOR in[2].
    check_gray2_is_in1_xor_in2: assert property (
        @(posedge clk) gray_out[2] == (in[1] ^ in[2])
    );

    // gray_out[3] equals in[2] XOR in[3].
    check_gray3_is_in2_xor_in3: assert property (
        @(posedge clk) gray_out[3] == (in[2] ^ in[3])
    );

    // Vector mapping: gray_out == {in[2]^in[3], in[1]^in[2], in[0]^in[1], in[0]}.
    check_vector_mapping: assert property (
        @(posedge clk) gray_out == { (in[2] ^ in[3]), (in[1] ^ in[2]), (in[0] ^ in[1]), in[0] }
    );

    // Outputs remain stable if inputs are stable between cycles.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(gray_out)
    );
endmodule