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

// ADD mode: SUM is I0 ^ I1 ^ CIN.
    check_add_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0000) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

// ADD mode: COUT is (I0 & I1) | (CIN & (I0 ^ I1)).
    check_add_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0000) |-> (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
    );

// SUB mode: SUM is I0 ^ I1 ^ CIN.
    check_sub_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0001) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

// SUB mode: COUT is (~I0 & I1) | (CIN & (~I0 ^ I1)).
    check_sub_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0001) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

// ADDSUB mode with I3=1: behaves like ADD.
    check_addsub_add_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0010 && I3 == 1'b1) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

// ADDSUB mode with I3=1: behaves like ADD.
    check_addsub_add_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0010 && I3 == 1'b1) |-> (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
    );

// ADDSUB mode with I3=0: behaves like SUB.
    check_addsub_sub_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0010 && I3 == 1'b0) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

// ADDSUB mode with I3=0: behaves like SUB.
    check_addsub_sub_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0010 && I3 == 1'b0) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

// NE mode: SUM is ~(I0 ^ I1).
    check_ne_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0011) |-> (SUM == ~(I0 ^ I1))
    );

// NE mode: COUT is 1'b1.
    check_ne_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0011) |-> (COUT == 1'b1)
    );

// GE mode: SUM is ~(I0 ^ I1).
    check_ge_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0100) |-> (SUM == ~(I0 ^ I1))
    );

// GE mode: COUT is (~I0 & I1) | (CIN & (~I0 ^ I1)).
    check_ge_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0100) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

// LE mode: SUM is ~(I0 ^ I1).
    check_le_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0101) |-> (SUM == ~(I0 ^ I1))
    );

// LE mode: COUT is (I0 & I1) | (CIN & (I0 | I1)).
    check_le_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0101) |-> (COUT == ((I0 & I1) | (CIN & (I0 | I1))))
    );

// CUP mode: SUM is I0.
    check_cup_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0110) |-> (SUM == I0)
    );

// CUP mode: COUT is 1'b0.
    check_cup_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0110) |-> (COUT == 1'b0)
    );

// CDN mode: SUM is ~I0.
    check_cdn_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b0111) |-> (SUM == ~I0)
    );

// CDN mode: COUT is 1'b1.
    check_cdn_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b0111) |-> (COUT == 1'b1)
    );

// CUPCDN mode with I3=1: behaves like CUP.
    check_cupcdn_cup_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b1000 && I3 == 1'b1) |-> (SUM == I0)
    );

// CUPCDN mode with I3=1: behaves like CUP.
    check_cupcdn_cup_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b1000 && I3 == 1'b1) |-> (COUT == 1'b0)
    );

// CUPCDN mode with I3=0: behaves like CDN.
    check_cupcdn_cdn_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b1000 && I3 == 1'b0) |-> (SUM == ~I0)
    );

// CUPCDN mode with I3=0: behaves like CDN.
    check_cupcdn_cdn_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b1000 && I3 == 1'b0) |-> (COUT == 1'b1)
    );

// MULT mode: SUM is I0 & I1.
    check_mult_sum: assert property (
        @(posedge clk) (ALU_MODE == 4'b1001) |-> (SUM == (I0 & I1))
    );

// MULT mode: COUT is I0 & I1.
    check_mult_cout: assert property (
        @(posedge clk) (ALU_MODE == 4'b1001) |-> (COUT == (I0 & I1))
    );

// Unsupported mode: SUM is 1'b0.
    check_default_sum: assert property (
        @(posedge clk) (ALU_MODE >= 4'b1010) |-> (SUM == 1'b0)
    );

// Unsupported mode: COUT is 1'b0.
    check_default_cout: assert property (
        @(posedge clk) (ALU_MODE >= 4'b1010) |-> (COUT == 1'b0)
    );

endmodule
