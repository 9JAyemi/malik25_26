// SVA bind module for MUXF7
module MUXF7_sva (
  input logic O,
  input logic I0, I1, I2, I3, I4, I5, I6,
  input logic S
);

  // Note: DUT uses 3-bit case items on a 1-bit S.
  // Behavior is effectively 2:1 (I0/I1) with default 0 on X/Z S.
  initial begin
    assert ($bits(S) == 3)
      else $warning("MUXF7: S is %0d-bit; case items are 3-bit -> behavior reduces to 2:1 mux (I0/I1) with default 0 on X/Z S.", $bits(S));
  end

  // Expected output per actual RTL semantics (with 1-bit S)
  function automatic logic exp_O (logic S_i, logic I0_i, I1_i, I2_i, I3_i, I4_i, I5_i, I6_i);
    case (S_i)
      1'b0: exp_O = I0_i;
      1'b1: exp_O = I1_i;
      default: exp_O = 1'b0;
    endcase
  endfunction

  // Sample on any input change; use ##0 to evaluate after DUT settles
  `define MUXF7_EVT (I0 or I1 or I2 or I3 or I4 or I5 or I6 or S)

  // Functional correctness (single concise check)
  a_func: assert property (@(`MUXF7_EVT) 1'b1 |-> ##0 (O === exp_O(S,I0,I1,I2,I3,I4,I5,I6)));

  // Known-propagation when select and selected input are known
  a_known_sel0: assert property (@(`MUXF7_EVT) (S===1'b0 && !$isunknown(I0)) |-> ##0 (O===I0 && !$isunknown(O)));
  a_known_sel1: assert property (@(`MUXF7_EVT) (S===1'b1 && !$isunknown(I1)) |-> ##0 (O===I1 && !$isunknown(O)));

  // Default behavior on X/Z select
  a_default_Sxz: assert property (@(`MUXF7_EVT) ((S!==1'b0) && (S!==1'b1)) |-> ##0 (O===1'b0));

  // Isolation: unselected inputs do not affect O
  a_iso_sel0: assert property (@(`MUXF7_EVT)
                               (S===1'b0 && !$changed(I0) && $changed({I1,I2,I3,I4,I5,I6}))
                               |-> ##0 $stable(O));
  a_iso_sel1: assert property (@(`MUXF7_EVT)
                               (S===1'b1 && !$changed(I1) && $changed({I0,I2,I3,I4,I5,I6}))
                               |-> ##0 $stable(O));

  // Coverage: exercise each path and dynamic propagation
  c_sel0:   cover property (@(`MUXF7_EVT) S===1'b0);
  c_sel1:   cover property (@(`MUXF7_EVT) S===1'b1);
  c_def:    cover property (@(`MUXF7_EVT) (S!==1'b0) && (S!==1'b1));

  c_tog0:   cover property (@(`MUXF7_EVT) (S===1'b0 && $changed(I0)) |-> ##0 $changed(O));
  c_tog1:   cover property (@(`MUXF7_EVT) (S===1'b1 && $changed(I1)) |-> ##0 $changed(O));

endmodule

// Bind into the DUT
bind MUXF7 MUXF7_sva sva_muxf7 (.*);