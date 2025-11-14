// SVA for sky130_fd_sc_hs__dlygate4sd2
// Bind into the DUT to observe internal delay_count
bind sky130_fd_sc_hs__dlygate4sd2 dlygate4sd2_sva i_dlygate4sd2_sva (
  .A(A), .VPWR(VPWR), .VGND(VGND), .X(X), .delay_count(delay_count)
);

module dlygate4sd2_sva (
  input  logic       A,
  input  logic       VPWR,
  input  logic       VGND,
  input  logic       X,
  input  logic [3:0] delay_count
);

  // Past-valid guard for $past usage on the VPWR clock
  logic past_vld;
  always @(posedge VPWR or negedge VGND) begin
    if (!VGND) past_vld <= 1'b0;
    else       past_vld <= 1'b1;
  end

  default clocking cb @ (posedge VPWR); endclocking

  // 1) Asynchronous/synchronous reset behavior drives X low and does not change counter
  assert property (@(negedge VGND) ##0 (X == 1'b0) and $stable(delay_count))
    else $error("X not forced low or delay_count changed on negedge VGND");

  assert property (cb (VGND == 1'b0) |-> ##0 (X == 1'b0) and $stable(delay_count))
    else $error("X not forced low or delay_count changed when VGND==0 at posedge VPWR");

  // 2) Load on A==1: counter to 15, X to 0 (takes priority over decrement)
  assert property (cb disable iff (!VGND) A |-> ##0 (delay_count == 4'hF && X == 1'b0))
    else $error("Load on A==1 failed (delay_count!=15 or X!=0)");

  // 3) Decrement while counting (A==0 and count>0), X holds its previous value
  assert property (cb disable iff (!VGND)
                   (past_vld && !A && (delay_count > 0))
                   |-> ##0 (delay_count == $past(delay_count)-1) && (X == $past(X)))
    else $error("Decrement or X hold failed while counting");

  // 4) When count is zero and A==0, X must be 1 and counter holds
  assert property (cb disable iff (!VGND)
                   (!A && (delay_count == 0)) |-> ##0 (X == 1'b1 && $stable(delay_count)))
    else $error("X not asserted or delay_count changed at terminal state");

  // 5) Safety invariants
  // X cannot be 1 when VGND==0, or when A==1, or when delay_count>0
  assert property (cb (VGND==0) |-> ##0 (X==0))
    else $error("X high while VGND==0");
  assert property (cb A |-> ##0 (X==0))
    else $error("X high while A==1");
  assert property (cb (delay_count > 0) |-> ##0 (X==0))
    else $error("X high while delay_count>0");

  // If X is 1 after an update, we must be in the done state with A==0 and VGND==1 and count==0
  assert property (cb (X == 1'b1) |-> (VGND==1'b1 && !A && delay_count==0))
    else $error("X==1 outside of done state");

  // 6) Multi-cycle timing: After a load, 16 consecutive low-A cycles yield X==1 (if not reset)
  sequence s_16_lowA; (!A && VGND)[*16]; endsequence
  assert property (cb disable iff (!VGND) A ##1 s_16_lowA ##0 (X==1))
    else $error("X did not assert after 16 low-A cycles following load");

  // 7) Basic X knownness at sampled times
  assert property (cb !$isunknown(X))
    else $error("X unknown at posedge VPWR");

  // ----------------
  // Useful coverage
  // ----------------
  // Cover reset event
  cover property (@(negedge VGND) ##0 (X==0));

  // Cover full countdown completion (A high then 16 low cycles to X==1)
  cover property (cb disable iff (!VGND) A ##1 s_16_lowA ##0 (X==1));

  // Cover reload before completion (early A==1 while counting)
  cover property (cb disable iff (!VGND)
                  A ##1 (!A && (delay_count>0))[*1:15] ##1 A);

  // Cover X 0->1 transition at done
  cover property (cb disable iff (!VGND)
                  ($past(X)==0 && X==1 && delay_count==0 && !A));

endmodule