module mux_4to1_sva (
    input logic clk,           // external verification clock
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [31:0] C,
    input logic [31:0] D,
    input logic [1:0]  S,
    input logic [31:0] Y
);
    // Analysis: No clock/reset in DUT; pure combinational 4:1 mux. This wrapper samples on clk.

    default clocking cb @(posedge clk); endclocking

    // When S==00, Y must equal A.
    check_s00_selects_A: assert property ( (S == 2'b00) |-> (Y == A) );

    // When S==01, Y must equal B.
    check_s01_selects_B: assert property ( (S == 2'b01) |-> (Y == B) );

    // When S==10, Y must equal C.
    check_s10_selects_C: assert property ( (S == 2'b10) |-> (Y == C) );

    // When S==11, Y must equal D.
    check_s11_selects_D: assert property ( (S == 2'b11) |-> (Y == D) );

    // With S==00 and both S and A stable, Y must be stable.
    stable_y_when_s00_and_A_stable: assert property ( (S == 2'b00) && $stable(S) && $stable(A) |-> $stable(Y) );

    // With S==01 and both S and B stable, Y must be stable.
    stable_y_when_s01_and_B_stable: assert property ( (S == 2'b01) && $stable(S) && $stable(B) |-> $stable(Y) );

    // With S==10 and both S and C stable, Y must be stable.
    stable_y_when_s10_and_C_stable: assert property ( (S == 2'b10) && $stable(S) && $stable(C) |-> $stable(Y) );

    // With S==11 and both S and D stable, Y must be stable.
    stable_y_when_s11_and_D_stable: assert property ( (S == 2'b11) && $stable(S) && $stable(D) |-> $stable(Y) );

endmodule