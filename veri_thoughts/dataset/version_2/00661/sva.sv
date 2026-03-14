module FA_29_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);
    // S equals three-input XOR of A, B, and Ci.
    check_sum_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) S == (A ^ B ^ Ci)
    );

    // Co equals majority function (A&B) | (A&Ci) | (B&Ci).
    check_carry_definition: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ((A & B) | (A & Ci) | (B & Ci))
    );

    // Outputs remain stable if all inputs remain stable between cycles.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A) && $stable(B) && $stable(Ci)) |-> ($stable(S) && $stable(Co))
    );

    // Truth table: A=0, B=0, Ci=0 -> S=0, Co=0.
    truth_000: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A && !B && !Ci) |-> (S == 1'b0 && Co == 1'b0)
    );

    // Truth table: A=0, B=0, Ci=1 -> S=1, Co=0.
    truth_001: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A && !B && Ci) |-> (S == 1'b1 && Co == 1'b0)
    );

    // Truth table: A=0, B=1, Ci=0 -> S=1, Co=0.
    truth_010: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A && B && !Ci) |-> (S == 1'b1 && Co == 1'b0)
    );

    // Truth table: A=0, B=1, Ci=1 -> S=0, Co=1.
    truth_011: assert property (
        @(posedge CLK) disable iff (!RESETn) (!A && B && Ci) |-> (S == 1'b0 && Co == 1'b1)
    );

    // Truth table: A=1, B=0, Ci=0 -> S=1, Co=0.
    truth_100: assert property (
        @(posedge CLK) disable iff (!RESETn) (A && !B && !Ci) |-> (S == 1'b1 && Co == 1'b0)
    );

    // Truth table: A=1, B=0, Ci=1 -> S=0, Co=1.
    truth_101: assert property (
        @(posedge CLK) disable iff (!RESETn) (A && !B && Ci) |-> (S == 1'b0 && Co == 1'b1)
    );

    // Truth table: A=1, B=1, Ci=0 -> S=0, Co=1.
    truth_110: assert property (
        @(posedge CLK) disable iff (!RESETn) (A && B && !Ci) |-> (S == 1'b0 && Co == 1'b1)
    );

    // Truth table: A=1, B=1, Ci=1 -> S=1, Co=1.
    truth_111: assert property (
        @(posedge CLK) disable iff (!RESETn) (A && B && Ci) |-> (S == 1'b1 && Co == 1'b1)
    );

endmodule