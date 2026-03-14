module sky130_fd_sc_ms__fahcin_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);
    // SUM equals A ^ B ^ ~CIN.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ ~CIN)
    );

    // When CIN==1, SUM equals A ^ B.
    check_sum_when_cin1: assert property (
        @(posedge clk) (CIN == 1'b1) |-> (SUM == (A ^ B))
    );

    // When CIN==0, SUM equals ~(A ^ B).
    check_sum_when_cin0: assert property (
        @(posedge clk) (CIN == 1'b0) |-> (SUM == ~(A ^ B))
    );

    // When A == B, SUM equals ~CIN.
    check_sum_when_a_eq_b: assert property (
        @(posedge clk) (A == B) |-> (SUM == ~CIN)
    );

    // When A != B, SUM equals CIN.
    check_sum_when_a_ne_b: assert property (
        @(posedge clk) (A != B) |-> (SUM == CIN)
    );

    // COUT equals (A & B) | (A & ~CIN) | (B & ~CIN).
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (A & ~CIN) | (B & ~CIN))
    );

    // When CIN==1, COUT equals A & B.
    check_cout_when_cin1: assert property (
        @(posedge clk) (CIN == 1'b1) |-> (COUT == (A & B))
    );

    // When CIN==0, COUT equals A | B.
    check_cout_when_cin0: assert property (
        @(posedge clk) (CIN == 1'b0) |-> (COUT == (A | B))
    );

    // When A==0 and B==0, COUT is 0.
    check_cout_ab00_zero: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b0)) |-> (COUT == 1'b0)
    );

    // When A==1 and B==1, COUT is 1.
    check_cout_ab11_one: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b1)) |-> (COUT == 1'b1)
    );

    // When A==0 and B==1, COUT equals ~CIN.
    check_cout_a0b1: assert property (
        @(posedge clk) ((A == 1'b0) && (B == 1'b1)) |-> (COUT == ~CIN)
    );

    // When A==1 and B==0, COUT equals ~CIN.
    check_cout_a1b0: assert property (
        @(posedge clk) ((A == 1'b1) && (B == 1'b0)) |-> (COUT == ~CIN)
    );
endmodule