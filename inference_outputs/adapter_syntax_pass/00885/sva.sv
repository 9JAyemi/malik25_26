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

    // a_prim is the first round a value.
    check_a_prim_round_1: assert property (
        @(posedge clk)
        a_prim == ((a + b) + {((a + b) ^ d), 16'h0000})
    );

    // b_prim is the final b rotation of the first round.
    check_b_prim_round_1: assert property (
        @(posedge clk)
        b_prim == {((a + b) ^ d), 16'h0000}
    );

    // c_prim is the first round c value.
    check_c_prim_round_1: assert property (
        @(posedge clk)
        c_prim == ((c + {((a + b) ^ d), 16'h0000}) + {((a + b) ^ d), 16'h0000})
    );

    // d_prim is the final d rotation of the first round.
    check_d_prim_round_1: assert property (
        @(posedge clk)
        d_prim == {((a + b) ^ d), 16'h0000}
    );

    // a_prim and d_prim are identical after the first round.
    check_a_d_prim_equal: assert property (
        @(posedge clk)
        a_prim == d_prim
    );

    // c_prim is the sum of the two first-round c rotations.
    check_c_prim_sum: assert property (
        @(posedge clk)
        c_prim == (((c + {((a + b) ^ d), 16'h0000}) + {((a + b) ^ d), 16'h0000}) +
                   ((c + {((a + b) ^ d), 16'h0000}) + {((a + b) ^ d), 16'h0000}))
    );

    // b_prim and c_prim are identical after the first round.
    check_b_c_prim_equal: assert property (
        @(posedge clk)
        b_prim == c_prim
    );

    // b_prim and d_prim are identical after the first round.
    check_b_d_prim_equal: assert property (
        @(posedge clk)
        b_prim == d_prim
    );

endmodule