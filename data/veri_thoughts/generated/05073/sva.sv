module alu_sva (
    input logic clk,
    input logic I0,
    input logic I1,
    input logic I3,
    input logic CIN,
    input logic [3:0] ALU_MODE,
    input logic SUM,
    input logic COUT
);

    // Sampling-clocked assertions; the RTL has no native clock or reset.

    // ADD mode computes full-adder sum and carry.
    check_add_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0000) |-> (
            (SUM  == (I0 ^ I1 ^ CIN)) &&
            (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
        )
    );

    // SUB mode computes the RTL's subtract carry/borrow expression.
    check_sub_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0001) |-> (
            (SUM  == (I0 ^ I1 ^ CIN)) &&
            (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
        )
    );

    // ADDSUB mode uses ADD behavior when I3 is high.
    check_addsub_add_path: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b0010) && I3) |-> (
            (SUM  == (I0 ^ I1 ^ CIN)) &&
            (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
        )
    );

    // ADDSUB mode uses SUB behavior when I3 is low.
    check_addsub_sub_path: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b0010) && !I3) |-> (
            (SUM  == (I0 ^ I1 ^ CIN)) &&
            (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
        )
    );

    // NE mode drives XNOR on SUM and constant high on COUT.
    check_ne_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0011) |-> (
            (SUM  == ~(I0 ^ I1)) &&
            (COUT == 1'b1)
        )
    );

    // GE mode drives XNOR on SUM and the SUB-style COUT expression.
    check_ge_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0100) |-> (
            (SUM  == ~(I0 ^ I1)) &&
            (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
        )
    );

    // LE mode drives XNOR on SUM and the RTL's LE carry expression.
    check_le_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0101) |-> (
            (SUM  == ~(I0 ^ I1)) &&
            (COUT == ((I0 & I1) | (CIN & (I0 | I1))))
        )
    );

    // CUP mode passes I0 to SUM and clears COUT.
    check_cup_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0110) |-> (
            (SUM  == I0) &&
            (COUT == 1'b0)
        )
    );

    // CDN mode inverts I0 on SUM and sets COUT.
    check_cdn_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0111) |-> (
            (SUM  == ~I0) &&
            (COUT == 1'b1)
        )
    );

    // CUPCDN mode uses CUP behavior when I3 is high.
    check_cupcdn_cup_path: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b1000) && I3) |-> (
            (SUM  == I0) &&
            (COUT == 1'b0)
        )
    );

    // CUPCDN mode uses CDN behavior when I3 is low.
    check_cupcdn_cdn_path: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b1000) && !I3) |-> (
            (SUM  == ~I0) &&
            (COUT == 1'b1)
        )
    );

    // MULT mode drives both outputs with I0 AND I1.
    check_mult_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b1001) |-> (
            (SUM  == (I0 & I1)) &&
            (COUT == (I0 & I1))
        )
    );

    // Unsupported modes drive both outputs low.
    check_default_modes: assert property (
        @(posedge clk)
        (ALU_MODE[3] && (ALU_MODE[2] || ALU_MODE[1])) |-> (
            (SUM  == 1'b0) &&
            (COUT == 1'b0)
        )
    );

endmodule