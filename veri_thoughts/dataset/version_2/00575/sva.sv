module adder_N4_14_sva (
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Ci,
    input  logic [3:0]  S,
    input  logic        Co
);
    // With Ci=0, S equals low 4 bits of A+B.
    check_sum_when_ci0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b0) |-> (S == ({1'b0,A} + {1'b0,B})[3:0])
    );

    // With Ci=1, S equals low 4 bits of A+B+1.
    check_sum_when_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> (S == ({1'b0,A} + {1'b0,B} + 5'd1)[3:0])
    );

    // Co equals bit[3] of (A+B+1)'s 4-bit sum, independent of Ci.
    check_co_is_sum1_bit3: assert property (
        @(posedge CLK) disable iff (!RESETn) Co == ({1'b0,A} + {1'b0,B} + 5'd1)[3]
    );

    // When Ci=1, Co must equal S[3] (since S selects the Ci=1 path).
    check_co_equals_s3_when_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> (Co == S[3])
    );

    // LSB behavior with Ci=0: S[0] == A[0] ^ B[0].
    check_lsb_xor_when_ci0: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b0) |-> (S[0] == (A[0] ^ B[0]))
    );

    // LSB behavior with Ci=1: S[0] == ~(A[0] ^ B[0]).
    check_lsb_notxor_when_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (Ci == 1'b1) |-> (S[0] == ~(A[0] ^ B[0]))
    );

    // If A, B, and Ci are stable across a cycle, S and Co must be stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $stable({A,B,Ci}) |-> $stable({S,Co})
    );

    // Co is independent of Ci: toggling Ci with A,B stable does not change Co.
    check_co_independent_of_ci: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable({A,B}) && $changed(Ci)) |-> $stable(Co)
    );

    // Identity: with A=0, B=0, Ci=0, S=0.
    check_zero_identity_ci0: assert property (
        @(posedge CLK) disable iff (!RESETn) (A==4'd0 && B==4'd0 && Ci==1'b0) |-> (S==4'd0)
    );

    // Identity: with A=0, B=0, Ci=1, S=1 and Co=0.
    check_zero_identity_ci1: assert property (
        @(posedge CLK) disable iff (!RESETn) (A==4'd0 && B==4'd0 && Ci==1'b1) |-> (S==4'd1 && Co==1'b0)
    );
endmodule