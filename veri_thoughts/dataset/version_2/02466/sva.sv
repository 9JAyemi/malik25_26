module adder16_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic CIN,
    input logic [15:0] SUM,
    input logic COUT
);
    // SUM and COUT equal the 17-bit sum of A, B, and CIN.
    check_full_sum: assert property (
        @(posedge CLK) {COUT, SUM} == (A + B + CIN)
    );

    // SUM equals the lower 16 bits of A + B + CIN.
    check_sum_low16: assert property (
        @(posedge CLK) SUM == (A + B + CIN)[15:0]
    );

    // COUT equals the carry-out bit of A + B + CIN.
    check_cout_bit16: assert property (
        @(posedge CLK) COUT == (A + B + CIN)[16]
    );

    // Adding zero B with CIN=0 yields SUM=A and no carry.
    check_add_zero_B: assert property (
        @(posedge CLK) (B == 16'h0000 && CIN == 1'b0) |-> (SUM == A && COUT == 1'b0)
    );

    // Adding zero A with CIN=0 yields SUM=B and no carry.
    check_add_zero_A: assert property (
        @(posedge CLK) (A == 16'h0000 && CIN == 1'b0) |-> (SUM == B && COUT == 1'b0)
    );

    // Zero A and B yield SUM=CIN and no carry.
    check_zero_plus_zero: assert property (
        @(posedge CLK) (A == 16'h0000 && B == 16'h0000) |-> (SUM == {15'b0, CIN} && COUT == 1'b0)
    );

    // 0xFFFF + 0x0000 + 1 -> SUM=0x0000, COUT=1.
    check_max_plus_one: assert property (
        @(posedge CLK) (A == 16'hFFFF && B == 16'h0000 && CIN == 1'b1) |-> (SUM == 16'h0000 && COUT == 1'b1)
    );

    // 0xFFFF + 0xFFFF + 0 -> SUM=0xFFFE, COUT=1.
    check_max_plus_max_nocin: assert property (
        @(posedge CLK) (A == 16'hFFFF && B == 16'hFFFF && CIN == 1'b0) |-> (SUM == 16'hFFFE && COUT == 1'b1)
    );

    // 0xFFFF + 0xFFFF + 1 -> SUM=0xFFFF, COUT=1.
    check_max_plus_max_cin: assert property (
        @(posedge CLK) (A == 16'hFFFF && B == 16'hFFFF && CIN == 1'b1) |-> (SUM == 16'hFFFF && COUT == 1'b1)
    );

    // A + ~A with CIN=0 -> SUM=0xFFFF, COUT=0.
    check_complement_nocin: assert property (
        @(posedge CLK) (B == ~A && CIN == 1'b0) |-> (SUM == 16'hFFFF && COUT == 1'b0)
    );

    // A + ~A with CIN=1 -> SUM=0x0000, COUT=1.
    check_complement_cin: assert property (
        @(posedge CLK) (B == ~A && CIN == 1'b1) |-> (SUM == 16'h0000 && COUT == 1'b1)
    );
endmodule