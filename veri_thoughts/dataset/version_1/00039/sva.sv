// SVA for Deco_Round_Mult
module Deco_Round_Mult_sva (
  input logic [1:0] round_mode,
  input logic or_info,
  input logic xor_info,
  input logic ctrl
);

  // Knownness: if inputs are known, output must be known
  assert property (@(round_mode or or_info or xor_info or ctrl)
                   !$isunknown({round_mode,or_info,xor_info}) |-> !$isunknown(ctrl))
    else $error("ctrl is X/Z with known inputs");

  // Functional equivalence (when inputs are known)
  assert property (@(round_mode or or_info or xor_info or ctrl)
                   !$isunknown({round_mode,or_info,xor_info})
                   |-> (ctrl === (or_info &&
                                   ((round_mode==2'b01 && xor_info) ||
                                    (round_mode==2'b10 && !xor_info)))))
    else $error("ctrl decode mismatch");

  // Sanity: if or_info is 0, ctrl must be 0 (regardless of round_mode/xor_info if known)
  assert property (@(round_mode or or_info or xor_info or ctrl)
                   !$isunknown(or_info) && (or_info==1'b0) |-> (ctrl===1'b0))
    else $error("ctrl not 0 when or_info=0");

  // Coverage: exercise all meaningful decode combinations
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b01) && !xor_info && (ctrl==1'b0));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b01) &&  xor_info && (ctrl==1'b1));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b10) && !xor_info && (ctrl==1'b1));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b10) &&  xor_info && (ctrl==1'b0));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b00) && (ctrl==1'b0));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  or_info && (round_mode==2'b11) && (ctrl==1'b0));
  cover property (@(round_mode or or_info or xor_info or ctrl)
                  !or_info && (ctrl==1'b0));

endmodule

bind Deco_Round_Mult Deco_Round_Mult_sva sva_i (.*);