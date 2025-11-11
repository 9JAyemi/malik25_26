// SVA for sky130_fd_sc_hd__or2b
// Bind with: bind sky130_fd_sc_hd__or2b sky130_fd_sc_hd__or2b_sva i_or2b_sva (.*);

module sky130_fd_sc_hd__or2b_sva (
    input logic A,
    input logic B_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // Treat any change on pins as a sampling event
    default clocking cb @(
        posedge A or negedge A or
        posedge B_N or negedge B_N or
        posedge X or negedge X or
        posedge VPWR or negedge VPWR or
        posedge VGND or negedge VGND or
        posedge VPB  or negedge VPB  or
        posedge VNB  or negedge VNB
    ); endclocking

    // Helpers
    function automatic bit power_good_simple;
        power_good_simple = (VPWR === 1'b1) && (VGND === 1'b0);
    endfunction

    // Body ties must be correct at all times
    assert property (@cb (VPB === VPWR) && (VNB === VGND))
        else $error("Body-bias pins not tied to supplies: VPB!=VPWR or VNB!=VGND");

    // When powered and inputs known, X must be known
    assert property (@cb disable iff (!power_good_simple())
                     (!$isunknown({A,B_N})) |-> (!$isunknown(X)))
        else $error("X is X/Z while powered with known inputs");

    // When powered, any change on X must reflect the Boolean function X = A | B_N at that instant
    assert property (@(posedge X or negedge X)
                     disable iff (!power_good_simple())
                     X === (A | B_N))
        else $error("X changed to a value not equal to A|B_N");

    // When powered, if inputs are stable between consecutive samples, X must remain stable
    assert property (@cb disable iff (!power_good_simple())
                     ($stable(A) && $stable(B_N)) |=> $stable(X))
        else $error("X toggled without input change while powered");

    // When powered and inputs are stable and known now, X must equal the function (post any propagation)
    assert property (@cb disable iff (!power_good_simple())
                     (!$isunknown({A,B_N}) && $stable(A) && $stable(B_N)) |-> (X === (A | B_N)))
        else $error("X != A|B_N under stable, known inputs while powered");

    // Optional: X should only toggle when either input or power changes (guards against spurious glitches)
    assert property (@(posedge X or negedge X)
                     ( $changed(A) || $changed(B_N) || !$stable(VPWR) || !$stable(VGND) ))
        else $error("X toggled without input or power change");

    // ----------------
    // Functional coverage
    // ----------------

    // Power-good observed
    cover property (@cb power_good_simple());

    // Truth table coverage under power-good
    cover property (@cb power_good_simple() && (A==1'b0) && (B_N==1'b0) ##1 (X==1'b0));
    cover property (@cb power_good_simple() && (A==1'b0) && (B_N==1'b1) ##1 (X==1'b1));
    cover property (@cb power_good_simple() && (A==1'b1) && (B_N==1'b0) ##1 (X==1'b1));
    cover property (@cb power_good_simple() && (A==1'b1) && (B_N==1'b1) ##1 (X==1'b1));

    // Output edge coverage under power-good
    cover property (@(posedge X) power_good_simple());
    cover property (@(negedge X) power_good_simple());

endmodule