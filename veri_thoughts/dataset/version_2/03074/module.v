
module expand_key_type_B_256 (in, out_1, out_2);

    input      [255:0] in;
    output reg [255:0] out_1;
    output     [127:0] out_2;
    wire       [31:0]  k0, k1, k2, k3, k4, k5, k6, k7,
                       v5, v6, v7, k8;
    reg        [31:0]  k0a, k1a, k2a, k3a, k4a, k5a, k6a, k7a;
    wire       [31:0]  k0b, k1b, k2b, k3b, k4b, k5b, k6b, k7b;

    assign {k0, k1, k2, k3, k4, k5, k6, k7} = in;

    assign v5 = k4 ^ k5;
    assign v6 = v5 ^ k6;
    assign v7 = v6 ^ k7;

    always @ (*)
        {k0a, k1a, k2a, k3a, k4a, k5a, k6a, k7a} <= {k0, k1, k2, k3, k4, v5, v6, v7};

    S4 S4_0 (.in(k3), .out(k8));

    assign {k0b, k1b, k2b, k3b} = {k0a, k1a, k2a, k3a};
    assign k4b = k4a ^ k8;
    assign k5b = k5a ^ k8;
    assign k6b = k6a ^ k8;
    assign k7b = k7a ^ k8;

    always @ (*)
        out_1 <= {k0b, k1b, k2b, k3b, k4b, k5b, k6b, k7b};

    assign out_2 = {k4b, k5b, k6b, k7b};

endmodule

module S4 (in, out);

    input  [31:0] in;
    output [31:0] out;

    assign out = in ^ (in << 11) ^ (in << 22);

endmodule
