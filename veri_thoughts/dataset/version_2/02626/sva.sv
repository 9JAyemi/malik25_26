module ripple_carry_adder_sva (
    input  logic        CLK,   // External clock for SVA only; DUT has no clock/reset
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Cin,
    input  logic [3:0]  Sum,
    input  logic        Cout
);
    // Combinational ripple-carry adder: Sum[i]=Ai^Bi^carry_in, Cout from final carry

    let c0_exp = (A[0] & B[0]) | (A[0] & Cin) | (B[0] & Cin);
    let c1_exp = (A[1] & B[1]) | (A[1] & c0_exp) | (B[1] & c0_exp);
    let c2_exp = (A[2] & B[2]) | (A[2] & c1_exp) | (B[2] & c1_exp);

    // Sum[0] matches RTL expression A0 ^ B0 ^ Cin.
    check_sum0_matches_rtl: assert property (
        @(posedge CLK) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum[1] matches RTL expression A1 ^ B1 ^ C0.
    check_sum1_matches_rtl: assert property (
        @(posedge CLK) Sum[1] == (A[1] ^ B[1] ^ c0_exp)
    );

    // Sum[2] matches RTL expression A2 ^ B2 ^ C1.
    check_sum2_matches_rtl: assert property (
        @(posedge CLK) Sum[2] == (A[2] ^ B[2] ^ c1_exp)
    );

    // Sum[3] matches RTL expression A3 ^ B3 ^ C2.
    check_sum3_matches_rtl: assert property (
        @(posedge CLK) Sum[3] == (A[3] ^ B[3] ^ c2_exp)
    );

    // Cout matches RTL expression using A3, B3, and C2.
    check_cout_matches_rtl: assert property (
        @(posedge CLK) Cout == ((A[3] & B[3]) | (A[3] & c2_exp) | (B[3] & c2_exp))
    );

    // Full 5-bit result equals A + B + Cin.
    check_full_result_adds: assert property (
        @(posedge CLK) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Outputs are known when inputs are known.
    check_known_propagation: assert property (
        @(posedge CLK) (!$isunknown({A, B, Cin})) |-> (!$isunknown({Sum, Cout}))
    );

    // If B==0 and Cin==0 then Sum==A and Cout==0.
    check_identity_B_zero: assert property (
        @(posedge CLK) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == A) && (Cout == 1'b0))
    );

    // If A==0 and Cin==0 then Sum==B and Cout==0.
    check_identity_A_zero: assert property (
        @(posedge CLK) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == B) && (Cout == 1'b0))
    );

    // If B==4'hF and Cin==1 then {Cout,Sum} == {1,A}.
    check_full_carry_propagation: assert property (
        @(posedge CLK) ((B == 4'hF) && (Cin == 1'b1)) |-> ({Cout, Sum} == {1'b1, A})
    );

endmodule