module alu_sva (
    input logic I0,
    input logic I1,
    input logic I3,
    input logic CIN,
    input logic [3:0] ALU_MODE,
    input logic SUM,
    input logic COUT
);

    // ADD mode: SUM is the 1-bit XOR of I0, I1, and CIN.
    check_add_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0000) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

    // ADD mode: COUT is the full-adder carry of I0, I1, and CIN.
    check_add_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0000) |-> (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
    );

    // SUB mode: SUM is the 1-bit XOR of I0, I1, and CIN.
    check_sub_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0001) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

    // SUB mode: COUT is the full-subtractor borrow of I0, I1, and CIN.
    check_sub_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0001) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

    // ADDSUB mode with I3 high: behavior matches ADD.
    check_addsub_add_sum: assert property (
        @($global_clock) ((ALU_MODE == 4'b0010) && I3) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

    // ADDSUB mode with I3 high: COUT matches ADD.
    check_addsub_add_cout: assert property (
        @($global_clock) ((ALU_MODE == 4'b0010) && I3) |-> (COUT == ((I0 & I1) | (CIN & (I0 ^ I1))))
    );

    // ADDSUB mode with I3 low: behavior matches SUB.
    check_addsub_sub_sum: assert property (
        @($global_clock) ((ALU_MODE == 4'b0010) && !I3) |-> (SUM == (I0 ^ I1 ^ CIN))
    );

    // ADDSUB mode with I3 low: COUT matches SUB.
    check_addsub_sub_cout: assert property (
        @($global_clock) ((ALU_MODE == 4'b0010) && !I3) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

    // NE mode: SUM is the inverse of the bitwise XOR of I0 and I1.
    check_ne_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0011) |-> (SUM == ~(I0 ^ I1))
    );

    // NE mode: COUT is always high.
    check_ne_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0011) |-> (COUT == 1'b1)
    );

    // GE mode: SUM is the inverse of the bitwise XOR of I0 and I1.
    check_ge_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0100) |-> (SUM == ~(I0 ^ I1))
    );

    // GE mode: COUT is the full-subtractor borrow of I0, I1, and CIN.
    check_ge_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0100) |-> (COUT == ((~I0 & I1) | (CIN & (~I0 ^ I1))))
    );

    // LE mode: SUM is the inverse of the bitwise XOR of I0 and I1.
    check_le_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0101) |-> (SUM == ~(I0 ^ I1))
    );

    // LE mode: COUT is the full-adder carry of I0, I1, and CIN.
    check_le_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0101) |-> (COUT == ((I0 & I1) | (CIN & (I0 | I1))))
    );

    // CUP mode: SUM passes I0 through.
    check_cup_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0110) |-> (SUM == I0)
    );

    // CUP mode: COUT is always low.
    check_cup_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0110) |-> (COUT == 1'b0)
    );

    // CDN mode: SUM is the inverse of I0.
    check_cdn_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b0111) |-> (SUM == ~I0)
    );

    // CDN mode: COUT is always high.
    check_cdn_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b0111) |-> (COUT == 1'b1)
    );

    // CUPCDN mode with I3 high: behavior matches CUP.
    check_cupcdn_cup_sum: assert property (
        @($global_clock) ((ALU_MODE == 4'b1000) && I3) |-> (SUM == I0)
    );

    // CUPCDN mode with I3 high: COUT is always low.
    check_cupcdn_cup_cout: assert property (
        @($global_clock) ((ALU_MODE == 4'b1000) && I3) |-> (COUT == 1'b0)
    );

    // CUPCDN mode with I3 low: behavior matches CDN.
    check_cupcdn_cdn_sum: assert property (
        @($global_clock) ((ALU_MODE == 4'b1000) && !I3) |-> (SUM == ~I0)
    );

    // CUPCDN mode with I3 low: COUT is always high.
    check_cupcdn_cdn_cout: assert property (
        @($global_clock) ((ALU_MODE == 4'b1000) && !I3) |-> (COUT == 1'b1)
    );

    // MULT mode: SUM is the AND of I0 and I1.
    check_mult_sum: assert property (
        @($global_clock) (ALU_MODE == 4'b1001) |-> (SUM == (I0 & I1))
    );

    // MULT mode: COUT is the AND of I0 and I1.
    check_mult_cout: assert property (
        @($global_clock) (ALU_MODE == 4'b1001) |-> (COUT == (I0 & I1))
    );

endmodule