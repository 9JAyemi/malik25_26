module mux_4_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] S,
    input logic Y
);
    // S==2'b10 selects B to Y.
    check_s10_selects_B: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == B)
    );

    // S==2'b01 selects C to Y.
    check_s01_selects_C: assert property (
        @(posedge clk) (S == 2'b01) |-> (Y == C)
    );

    // When S bits are equal (00 or 11), Y equals D.
    check_equal_bits_select_D: assert property (
        @(posedge clk) (S[1] == S[0]) |-> (Y == D)
    );

    // Y matches the combinational function implemented by the RTL.
    check_function_equivalence: assert property (
        @(posedge clk) Y == ((S == 2'b10) ? ((S == 2'b00) ? A : B) : ((S == 2'b01) ? C : D))
    );

    // When S != 2'b10, Y follows (S==01)?C:D.
    check_not_10_branch: assert property (
        @(posedge clk) (S != 2'b10) |-> (Y == ((S == 2'b01) ? C : D))
    );

    // When S == 2'b10, Y follows (S==00)?A:B (which simplifies to B).
    check_10_branch: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == ((S == 2'b00) ? A : B))
    );
endmodule