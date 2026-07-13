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

    // ADD mode computes SUM and COUT from I0, I1, and CIN.
    check_add_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0000) |-> ((SUM == (I0 ^ I1 ^ CIN)) &&
                                   (COUT == ((I0 & I1) | (CIN & (I0 ^ I1)))))
    );

    // SUB mode computes SUM and COUT from I0, I1, and CIN.
    check_sub_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0001) |-> ((SUM == (I0 ^ I1 ^ CIN)) &&
                                   (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1)))))
    );

    // ADDSUB mode with I3 high behaves like ADD.
    check_addsub_add_mode: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b0010) && I3) |-> ((SUM == (I0 ^ I1 ^ CIN)) &&
                                            (COUT == ((I0 & I1) | (CIN & (I0 ^ I1)))))
    );

    // ADDSUB mode with I3 low behaves like SUB.
    check_addsub_sub_mode: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b0010) && !I3) |-> ((SUM == (I0 ^ I1 ^ CIN)) &&
                                             (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1)))))
    );

    // NE mode computes SUM and drives COUT high.
    check_ne_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0011) |-> ((SUM == ~(I0 ^ I1)) && (COUT == 1'b1))
    );

    // GE mode computes SUM and COUT from I0, I1, and CIN.
    check_ge_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0100) |-> ((SUM == ~(I0 ^ I1)) &&
                                   (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1)))))
    );

    // LE mode computes SUM and COUT from I0, I1, and CIN.
    check_le_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0101) |-> ((SUM == ~(I0 ^ I1)) &&
                                   (COUT == ((I0 & I1) | (CIN & (I0 | I1)))))
    );

    // CUP mode drives SUM high and COUT low.
    check_cup_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0110) |-> ((SUM == 1'b1) && (COUT == 1'b0))
    );

    // CDN mode drives SUM low and COUT high.
    check_cdn_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b0111) |-> ((SUM == 1'b0) && (COUT == 1'b1))
    );

    // CUPCDN mode with I3 high behaves like CUP.
    check_cupcdn_cup_mode: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b1000) && I3) |-> ((SUM == 1'b1) && (COUT == 1'b0))
    );

    // CUPCDN mode with I3 low behaves like CDN.
    check_cupcdn_cdn_mode: assert property (
        @(posedge clk)
        ((ALU_MODE == 4'b1000) && !I3) |-> ((SUM == 1'b0) && (COUT == 1'b1))
    );

    // MULT mode drives SUM and COUT equal to I0 & I1.
    check_mult_mode: assert property (
        @(posedge clk)
        (ALU_MODE == 4'b1001) |-> ((SUM == (I0 & I1)) && (COUT == (I0 & I1)))
    );

    // Unsupported modes drive both outputs low.
    check_default_mode: assert property (
        @(posedge clk)
        (ALU_MODE inside {4'b1010, 4'b1011, 4'b1100, 4'b1101, 4'b1110, 4'b1111}) |-> ((SUM == 1'b0) && (COUT == 1'b0))
    );

endmodule