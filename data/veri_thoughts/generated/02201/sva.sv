module mux4to1_4bit_sva (
    input  logic CLK,
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic [3:0] C,
    input  logic [3:0] D,
    input  logic       S0,
    input  logic       S1,
    input  logic [3:0] Y
);
    // Exact functional equivalence to the RTL expression.
    check_function_equivalence: assert property (
        @(posedge CLK) Y == ((S0 | S1) ? ((S0 & S1) ? D : C) : ((S0 & ~S1) ? B : A))
    );

    // When S1=0,S0=0, Y must equal A.
    check_sel_00_to_A: assert property (
        @(posedge CLK) (S1 == 1'b0 && S0 == 1'b0) |-> (Y == A)
    );

    // When S1=0,S0=1, Y must equal C.
    check_sel_01_to_C: assert property (
        @(posedge CLK) (S1 == 1'b0 && S0 == 1'b1) |-> (Y == C)
    );

    // When S1=1,S0=0, Y must equal C.
    check_sel_10_to_C: assert property (
        @(posedge CLK) (S1 == 1'b1 && S0 == 1'b0) |-> (Y == C)
    );

    // When S1=1,S0=1, Y must equal D.
    check_sel_11_to_D: assert property (
        @(posedge CLK) (S1 == 1'b1 && S0 == 1'b1) |-> (Y == D)
    );

    // When exactly one select is HIGH, Y must equal C.
    check_xor_select_to_C: assert property (
        @(posedge CLK) (S0 ^ S1) |-> (Y == C)
    );

    // When any select is HIGH, Y must be C or D per S0&S1.
    check_or_select_rule: assert property (
        @(posedge CLK) (S0 | S1) |-> (Y == ((S0 & S1) ? D : C))
    );

    // When both selects are LOW, Y must equal A.
    check_nor_select_to_A: assert property (
        @(posedge CLK) !(S0 | S1) |-> (Y == A)
    );

    // Changing B alone must not affect Y (B is never selected).
    check_B_irrelevant: assert property (
        @(posedge CLK)
            ($changed(B) && $stable(A) && $stable(C) && $stable(D) && $stable(S0) && $stable(S1)) |-> $stable(Y)
    );

    // With selects pointing to C or D (S0|S1==1), changing A alone must not affect Y.
    check_A_irrelevant_when_or1: assert property (
        @(posedge CLK)
            ((S0 | S1) && $stable(S0) && $stable(S1) && $changed(A) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(Y)
    );

    // With selects at 00, changing C alone must not affect Y (Y=A).
    check_C_irrelevant_when_00: assert property (
        @(posedge CLK)
            ((S1 == 1'b0 && S0 == 1'b0) && $stable(S0) && $stable(S1) && $changed(C) && $stable(A) && $stable(B) && $stable(D)) |-> $stable(Y)
    );

    // Unless selects are 11, changing D alone must not affect Y.
    check_D_irrelevant_when_not_11: assert property (
        @(posedge CLK)
            ((!(S0 && S1)) && $stable(S0) && $stable(S1) && $changed(D) && $stable(A) && $stable(B) && $stable(C)) |-> $stable(Y)
    );
endmodule