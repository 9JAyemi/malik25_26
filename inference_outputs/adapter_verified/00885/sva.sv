module chacha_qr_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] c,
    input logic [31:0] d,
    input logic [31:0] a_prim,
    input logic [31:0] b_prim,
    input logic [31:0] c_prim,
    input logic [31:0] d_prim
);

// a_prim is the rotated sum of a and b.
    check_a_prim_function: assert property (
        @(posedge clk) a_prim == ((a + b) + {32'b0, a[15:0], a[31:16]})
    );

// b_prim is the rotated sum of b and c.
    check_b_prim_function: assert property (
        @(posedge clk) b_prim == ((b + c) + {32'b0, b[19:0], b[31:20]})
    );

// c_prim is the rotated sum of c and d.
    check_c_prim_function: assert property (
        @(posedge clk) c_prim == ((c + d) + {32'b0, c[23:0], c[31:24]})
    );

// d_prim is the rotated sum of d and a.
    check_d_prim_function: assert property (
        @(posedge clk) d_prim == ((d + a) + {32'b0, d[24:0], d[31:25]})
    );

// a_prim equals the rotated sum of a and b.
    check_a_prim_rotated_sum: assert property (
        @(posedge clk) a_prim == ((a + b) + {32'b0, a[15:0], a[31:16]})
    );

// b_prim equals the rotated sum of b and c.
    check_b_prim_rotated_sum: assert property (
        @(posedge clk) b_prim == ((b + c) + {32'b0, b[19:0], b[31:20]})
    );

// c_prim equals the rotated sum of c and d.
    check_c_prim_rotated_sum: assert property (
        @(posedge clk) c_prim == ((c + d) + {32'b0, c[23:0], c[31:24]})
    );

// d_prim equals the rotated sum of d and a.
    check_d_prim_rotated_sum: assert property (
        @(posedge clk) d_prim == ((d + a) + {32'b0, d[24:0], d[31:25]})
    );

// The four outputs are the rotated sums of the four inputs.
    check_all_outputs_rotated_sum: assert property (
        @(posedge clk)
            {a_prim, b_prim, c_prim, d_prim} ==
            {((a + b) + {32'b0, a[15:0], a[31:16]}),
             ((b + c) + {32'b0, b[19:0], b[31:20]}),
             ((c + d) + {32'b0, c[23:0], c[31:24]}),
             ((d + a) + {32'b0, d[24:0], d[31:25]})}
    );

endmodule
