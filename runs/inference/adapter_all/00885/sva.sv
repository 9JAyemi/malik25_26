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

    // a_prim matches the RTL's a1 result.
    check_a_prim_matches_a1: assert property (
        @(posedge clk)
        a_prim == (
            {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]} ^
            {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]}
        )
    );

    // b_prim matches the RTL's b3 result.
    check_b_prim_matches_b3: assert property (
        @(posedge clk)
        b_prim == (
            {($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[31:24]})[24:0], ($past(b) ^ {($past(c) + {($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[31:16]})[23:0], ($past(d) ^ {($past(a) + $past(b))[15:0], ($past(a) + $past(b))[3