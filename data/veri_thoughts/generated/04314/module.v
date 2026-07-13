
module binary_to_gray_xor (
    input wire [2:0] in_vec,
    output wire [2:0] out_vec
);

    assign out_vec[0] = in_vec[0] ^ in_vec[1];
    assign out_vec[1] = in_vec[1] ^ in_vec[2];
    assign out_vec[2] = in_vec[2];

endmodule
module top_module (
    input wire [2:0] in_vec,
    output wire [2:0] out_vec
);
    wire [2:0] out_vec_int;

    binary_to_gray_xor gray_xor(
        .in_vec(in_vec),
        .out_vec(out_vec_int)
    );

    assign out_vec = out_vec_int ^ 3'b010;

endmodule