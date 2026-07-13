module adder_sva (
    // Analysis: no clock/reset in RTL; purely combinational; S = (C ? A - B : A + B) with 4-bit wrap.
    // Key signals: A[3:0], B[3:0], C (mode select), S[3:0] (result).
    // Assertions sample on an external clock 'clk'.
    input  logic        clk,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        C,
    input  logic [3:0]  S
);
    // Add mode: S equals low 4 bits of A+B when C==0.
    check_add_mode_result: assert property (
        @(posedge clk) (C == 1'b0) |-> (S == (A + B)[3:0])
    );

    // Sub mode: S equals low 4 bits of A-B when C==1.
    check_sub_mode_result: assert property (
        @(posedge clk) (C == 1'b1) |-> (S == (A - B)[3:0])
    );

    // Combinational determinism: if {A,B,C} are stable, S is stable.
    stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A,B,C}) |-> $stable(S)
    );

    // Identity for zero B: adding or subtracting zero yields A.
    identity_when_B_zero: assert property (
        @(posedge clk) (B == 4'h0) |-> (S == A)
    );

    // Add identity: when A is zero in add mode, S equals B.
    add_identity_A_zero: assert property (
        @(posedge clk) (C == 1'b0 && A == 4'h0) |-> (S == B)
    );

    // Sub equality: when A==B in sub mode, S is zero (mod-16).
    sub_zero_when_A_eq_B: assert property (
        @(posedge clk) (C == 1'b1 && A == B) |-> (S == 4'h0)
    );

    // Add invertibility (mod-16): in add mode, (S - A) mod 16 equals B.
    add_mode_invertibility: assert property (
        @(posedge clk) (C == 1'b0) |-> ((S - A)[3:0] == B)
    );

    // Sub invertibility (mod-16): in sub mode, (S + B) mod 16 equals A.
    sub_mode_invertibility: assert property (
        @(posedge clk) (C == 1'b1) |-> ((S + B)[3:0] == A)
    );
endmodule