module binary_to_gray_sva (
    input logic [3:0] in,
    input logic [3:0] out
);
    // out[0] must equal in[0].
    map_out0_eq_in0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        out[0] == in[0]
    );

    // out[1] must equal in[0] ^ in[1].
    map_out1_eq_in0_xor_in1: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        out[1] == (in[0] ^ in[1])
    );

    // out[2] must equal in[1] ^ in[2] ^ in[0].
    map_out2_eq_in1_xor_in2_xor_in0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        out[2] == (in[1] ^ in[2] ^ in[0])
    );

    // out[3] must equal in[2] ^ in[3] ^ in[1].
    map_out3_eq_in2_xor_in3_xor_in1: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        out[3] == (in[2] ^ in[3] ^ in[1])
    );

    // in[1] must equal out[1] ^ out[0].
    derive_in1_eq_out1_xor_out0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        in[1] == (out[1] ^ out[0])
    );

    // in[2] must equal out[2] ^ out[1].
    derive_in2_eq_out2_xor_out1: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        in[2] == (out[2] ^ out[1])
    );

    // out[2] ^ out[0] must equal in[1] ^ in[2].
    derive_in1_xor_in2_eq_out2_xor_out0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (out[2] ^ out[0]) == (in[1] ^ in[2])
    );

    // in[3] must equal out[3] ^ out[2] ^ in[0].
    derive_in3_eq_out3_xor_out2_xor_in0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        in[3] == (out[3] ^ out[2] ^ in[0])
    );

    // out[3] ^ out[1] ^ out[0] must equal in[2] ^ in[3].
    derive_in2_xor_in3_eq_out3_xor_out1_xor_out0: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        (out[3] ^ out[1] ^ out[0]) == (in[2] ^ in[3])
    );

    // in[2] must equal out[2] ^ out[0] ^ in[1].
    derive_in2_eq_out2_xor_out0_xor_in1: assert property (
        @(posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1] or posedge in[2] or negedge in[2] or posedge in[3] or negedge in[3])
        in[2] == (out[2] ^ out[0] ^ in[1])
    );
endmodule