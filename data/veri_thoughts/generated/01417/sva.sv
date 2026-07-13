module top_module_sva (
    input logic clk,
    input logic [3:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor,
    input logic [7:0] final_out
);
    // out_and equals (in0&in1)|(in2&in3)
    check_out_and_definition: assert property (
        @(posedge clk) out_and == ((in[0] & in[1]) | (in[2] & in[3]))
    );

    // out_or equals (in0|in1)&(in2|in3)
    check_out_or_definition: assert property (
        @(posedge clk) out_or == ((in[0] | in[1]) & (in[2] | in[3]))
    );

    // out_xor equals (in0^in1)&(in2^in3)
    check_out_xor_definition: assert property (
        @(posedge clk) out_xor == ((in[0] ^ in[1]) & (in[2] ^ in[3]))
    );

    // final_out[7:4] are zero (zero-extended)
    check_final_out_upper_zero: assert property (
        @(posedge clk) final_out[7:4] == 4'b0000
    );

    // final_out[3] is constant 0
    check_final_out_bit3_zero: assert property (
        @(posedge clk) final_out[3] == 1'b0
    );

    // final_out[2] mirrors out_and
    check_final_out_bit2_maps_out_and: assert property (
        @(posedge clk) final_out[2] == out_and
    );

    // final_out[1] mirrors out_or
    check_final_out_bit1_maps_out_or: assert property (
        @(posedge clk) final_out[1] == out_or
    );

    // final_out[0] mirrors out_xor
    check_final_out_bit0_maps_out_xor: assert property (
        @(posedge clk) final_out[0] == out_xor
    );

    // final_out fully matches function of inputs
    check_final_out_full_matches_inputs: assert property (
        @(posedge clk)
        final_out == {4'b0000, 1'b0,
                      ((in[0] & in[1]) | (in[2] & in[3])),
                      ((in[0] | in[1]) & (in[2] | in[3])),
                      ((in[0] ^ in[1]) & (in[2] ^ in[3]))}
    );

    // If out_xor is 1 then out_or must be 1
    check_out_xor_implies_out_or: assert property (
        @(posedge clk) out_xor |-> out_or
    );
endmodule