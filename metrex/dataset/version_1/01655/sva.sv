// SVA for mux4to1 and its mux2 primitives
// Concise, combinational checks and coverage

`timescale 1ns/1ps
`default_nettype none

module mux4to1_sva (
    input  logic A0, A1, A2, A3,
    input  logic S0, S1,
    input  logic X,
    input  logic mux_2to1_0_out,
    input  logic mux_2to1_1_out,
    input  logic mux_2to1_2_out
);
    logic expected;

    always_comb begin
        // Golden 4:1 mux function
        expected = S1 ? (S0 ? A3 : A2) : (S0 ? A1 : A0);

        // Functional correctness (when inputs known)
        if (!$isunknown({A0,A1,A2,A3,S0,S1})) begin
            assert (X === expected)
                else $error("mux4to1 functional mismatch");
            assert (!$isunknown(X))
                else $error("mux4to1 X/Z on output with known inputs");
        end

        // Internal mux chain correctness (when inputs known)
        if (!$isunknown({A0,A1,S0}))
            assert (mux_2to1_0_out === (S0 ? A1 : A0))
                else $error("mux_2to1_0_out mismatch");
        if (!$isunknown({A2,A3,S0}))
            assert (mux_2to1_1_out === (S0 ? A3 : A2))
                else $error("mux_2to1_1_out mismatch");
        if (!$isunknown({mux_2to1_0_out,mux_2to1_1_out,S1}))
            assert (mux_2to1_2_out === (S1 ? mux_2to1_1_out : mux_2to1_0_out))
                else $error("mux_2to1_2_out mismatch");

        // Redundant final mux must be identity for all 4-state values
        assert (X === mux_2to1_2_out)
            else $error("Redundant mux altered value");

        // Minimal functional coverage (selection paths exercised)
        cover (S1==1'b0 && S0==1'b0 && X===A0);
        cover (S1==1'b0 && S0==1'b1 && X===A1);
        cover (S1==1'b1 && S0==1'b0 && X===A2);
        cover (S1==1'b1 && S0==1'b1 && X===A3);
    end
endmodule

module mux2_sva (
    input  logic a, b, sel,
    input  logic out
);
    always_comb begin
        if (!$isunknown({a,b,sel}))
            assert (out === (sel ? b : a))
                else $error("mux2 mismatch");
        cover (sel==1'b0 && out===a);
        cover (sel==1'b1 && out===b);
    end
endmodule

// Bind SVA to DUTs
bind mux4to1 mux4to1_sva u_mux4to1_sva (
    .A0(A0), .A1(A1), .A2(A2), .A3(A3),
    .S0(S0), .S1(S1),
    .X(X),
    .mux_2to1_0_out(mux_2to1_0_out),
    .mux_2to1_1_out(mux_2to1_1_out),
    .mux_2to1_2_out(mux_2to1_2_out)
);

bind mux2 mux2_sva u_mux2_sva (
    .a(a), .b(b), .sel(sel), .out(out)
);

`default_nettype wire