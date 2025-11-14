// SVA checker for sky130_fd_sc_ms__o221a
// Function: X == ((A1|A2) & (B1|B2) & C1)
module sky130_fd_sc_ms__o221a_sva (
    input  A1, A2, B1, B2, C1,
    input  X,
    input  or0_out, or1_out, and0_out_X,
    input  VPWR, VPB, VGND, VNB
);

    wire power_good = (VPWR===1'b1) && (VPB===1'b1) && (VGND===1'b0) && (VNB===1'b0);
    default disable iff (!power_good);

    // Rails must be good whenever they change (covers time 0)
    assert property (@(VPWR or VPB or VGND or VNB) power_good);

    // Functional correctness (gate-level equivalence)
    assert property (@(A1 or A2 or B1 or B2 or C1 or X)
        !$isunknown({A1,A2,B1,B2,C1}) |-> X === ((A1||A2) && (B1||B2) && C1));

    // Structural checks on internal nets
    assert property (@(A1 or A2 or or1_out)
        !$isunknown({A1,A2}) |-> or1_out === (A1||A2));
    assert property (@(B1 or B2 or or0_out)
        !$isunknown({B1,B2}) |-> or0_out === (B1||B2));
    assert property (@(or0_out or or1_out or C1 or and0_out_X)
        !$isunknown({or0_out,or1_out,C1}) |-> and0_out_X === (or0_out && or1_out && C1));
    assert property (@(and0_out_X or X)
        !$isunknown(and0_out_X) |-> X === and0_out_X);

    // Output changes only when inputs change (no spurious toggles)
    assert property (@(A1 or A2 or B1 or B2 or C1 or X)
        $changed(X) |-> !$stable({A1,A2,B1,B2,C1}));

    // Targeted functional coverage of truth table corners
    cover property (@(A1 or A2 or B1 or B2 or C1 or X)
        (A1||A2) && (B1||B2) && C1 && X);
    cover property (@(A1 or A2 or B1 or B2 or C1 or X)
        !(A1||A2) && (B1||B2) && C1 && !X);
    cover property (@(A1 or A2 or B1 or B2 or C1 or X)
        (A1||A2) && !(B1||B2) && C1 && !X);
    cover property (@(A1 or A2 or B1 or B2 or C1 or X)
        (A1||A2) && (B1||B2) && !C1 && !X);
    cover property (@(A1 or A2 or B1 or B2 or C1 or X)
        !(A1||A2) && !(B1||B2) && !C1 && !X);

    // Toggle coverage
    cover property (@(A1) $rose(A1));  cover property (@(A1) $fell(A1));
    cover property (@(A2) $rose(A2));  cover property (@(A2) $fell(A2));
    cover property (@(B1) $rose(B1));  cover property (@(B1) $fell(B1));
    cover property (@(B2) $rose(B2));  cover property (@(B2) $fell(B2));
    cover property (@(C1) $rose(C1));  cover property (@(C1) $fell(C1));
    cover property (@(X)  $rose(X));   cover property (@(X)  $fell(X));

endmodule

// Bind into the DUT; .* connects ports and internal nets by name
bind sky130_fd_sc_ms__o221a sky130_fd_sc_ms__o221a_sva sva_i (.*);