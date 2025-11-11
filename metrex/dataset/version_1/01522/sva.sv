// SVA checker for mux21_reg
module mux21_reg_sva(
  input logic I0, I1, S, clk,
  input logic O
);

default clocking cb @(posedge clk); endclocking

bit past_valid;
always_ff @(posedge clk) past_valid <= 1'b1;

function automatic logic sel_val(logic s, logic i0, logic i1);
  return s ? i1 : i0;
endfunction

// Functional correctness: registered mux behavior
assert property (past_valid |-> O === sel_val($past(S), $past(I0), $past(I1)));

// No-X on O when selected input and S were known last cycle
assert property (past_valid &&
                 !$isunknown($past(S)) &&
                 !$isunknown(sel_val($past(S), $past(I0), $past(I1)))
                 |-> !$isunknown(O));

// Hold: if S and selected input are unchanged, O is stable
assert property (past_valid && (S == $past(S)) &&
                 (($past(S)==1'b0 && I0 == $past(I0)) ||
                  ($past(S)==1'b1 && I1 == $past(I1)))
                 |-> $stable(O));

// Coverage
cover property (past_valid && ($past(S)==1'b0) && O === $past(I0));
cover property (past_valid && ($past(S)==1'b1) && O === $past(I1));
cover property (past_valid && $changed(O));

endmodule

bind mux21_reg mux21_reg_sva u_mux21_reg_sva(.I0(I0), .I1(I1), .S(S), .clk(clk), .O(O));