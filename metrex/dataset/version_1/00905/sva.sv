// SVA for four_bit_adder (bindable checker focusing on saturating add/sub semantics)

module four_bit_adder_sva (
  input logic [3:0] A, B,
  input logic       C,
  input logic [3:0] Y,
  input logic       OVF
);

  // Helpers (compute ideal saturating behavior)
  let add5   = {1'b0, A} + {1'b0, B};
  let sub5   = {1'b0, A} - {1'b0, B};
  let y_add  = add5[4] ? 4'hF : add5[3:0];
  let ovf_add= add5[4];
  let y_sub  = sub5[4] ? 4'h0 : sub5[3:0];
  let ovf_sub= sub5[4];

  // X-prop: known outputs when inputs are known
  assert property (@(A or B or C) !$isunknown({A,B,C}) |-> ##0 !$isunknown({Y,OVF}))
    else $error("X/Z detected on outputs for known inputs");

  // Functional correctness: saturating add/sub
  assert property (@(A or B or C) (C==1'b0) |-> ##0 (Y==y_add && OVF==ovf_add))
    else $error("ADD mode mismatch (saturating add)");
  assert property (@(A or B or C) (C==1'b1) |-> ##0 (Y==y_sub && OVF==ovf_sub))
    else $error("SUB mode mismatch (saturating sub)");

  // Consistency: OVF only when clamped, and clamp value matches mode
  assert property (@(A or B or C) OVF |-> ##0 ((C==0 && Y==4'hF && ovf_add) ||
                                               (C==1 && Y==4'h0 && ovf_sub)))
    else $error("OVF asserted without correct clamp/value");

  // Explicitly forbid OVF in non-saturating cases (tightens intent)
  assert property (@(A or B or C) (!ovf_add && C==0) |-> ##0 (!OVF && Y==y_add))
    else $error("Unexpected OVF or Y in non-overflow ADD");
  assert property (@(A or B or C) (!ovf_sub && C==1) |-> ##0 (!OVF && Y==y_sub))
    else $error("Unexpected OVF or Y in non-underflow SUB");

  // Coverage
  cover property (@(A or B or C) (C==0 && ovf_add));      // addition overflow
  cover property (@(A or B or C) (C==0 && !ovf_add));     // addition normal
  cover property (@(A or B or C) (C==1 && ovf_sub));      // subtraction underflow
  cover property (@(A or B or C) (C==1 && !ovf_sub));     // subtraction normal
  cover property (@(A or B or C) (C==0 && OVF && Y==4'hF));
  cover property (@(A or B or C) (C==1 && OVF && Y==4'h0));
  cover property (@(posedge C)   $stable({A,B}));         // mode toggle with fixed operands
  cover property (@(negedge C)   $stable({A,B}));

endmodule

bind four_bit_adder four_bit_adder_sva sva_i (.*);