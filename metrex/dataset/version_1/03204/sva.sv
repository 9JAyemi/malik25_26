// SVA checker for mux4. Bind to DUT instance as shown at bottom.
module mux4_sva #(parameter int DW=99) (
  input logic [DW-1:0] out,
  input logic [DW-1:0] in0, in1, in2, in3,
  input logic          sel0, sel1, sel2, sel3
);
  wire [3:0] sels = {sel3, sel2, sel1, sel0};

  function automatic logic [DW-1:0] mux_expr(
    input logic [DW-1:0] a0,a1,a2,a3,
    input logic b0,b1,b2,b3
  );
    mux_expr = (b0 ? a0 : '0) |
               (b1 ? a1 : '0) |
               (b2 ? a2 : '0) |
               (b3 ? a3 : '0);
  endfunction

  // At most one select asserted (allow none)
  a_onehot0: assert property (@(*) $onehot0(sels))
    else $error("mux4: illegal multi-select");

  // Functional equivalence when all drivers are known
  a_equiv_known: assert property (@(*)
    !$isunknown({sels,in0,in1,in2,in3}) |->
      (out == mux_expr(in0,in1,in2,in3,sel0,sel1,sel2,sel3))
  ) else $error("mux4: functional mismatch");

  // No-select => zero
  a_none_zero: assert property (@(*) (sels==4'b0000) |-> (out=='0))
    else $error("mux4: out must be 0 when no select");

  // Single-select paths
  a_sel0: assert property (@(*) ( sel0 && !sel1 && !sel2 && !sel3) |-> (out==in0))
    else $error("mux4: sel0 path incorrect");
  a_sel1: assert property (@(*) (!sel0 &&  sel1 && !sel2 && !sel3) |-> (out==in1))
    else $error("mux4: sel1 path incorrect");
  a_sel2: assert property (@(*) (!sel0 && !sel1 &&  sel2 && !sel3) |-> (out==in2))
    else $error("mux4: sel2 path incorrect");
  a_sel3: assert property (@(*) (!sel0 && !sel1 && !sel2 &&  sel3) |-> (out==in3))
    else $error("mux4: sel3 path incorrect");

  // Out must be known when controls are known and either none or a single known input is selected
  a_known_out: assert property (@(*)
    (!$isunknown(sels) && $onehot0(sels) &&
     ((sels==4'b0000) ||
      (sel0 && !$isunknown(in0)) ||
      (sel1 && !$isunknown(in1)) ||
      (sel2 && !$isunknown(in2)) ||
      (sel3 && !$isunknown(in3))))
    |-> !$isunknown(out)
  ) else $error("mux4: unexpected X/Z on out");

  // Combinational consistency: if inputs/selects stable, out stable
  a_stable: assert property (@(*) $stable({in0,in1,in2,in3,sels}) |-> $stable(out))
    else $error("mux4: out changed without input/select change");

  // Coverage: exercise each path and the none-selected case
  c_sel0: cover property (@(*) ( sel0 && !sel1 && !sel2 && !sel3));
  c_sel1: cover property (@(*) (!sel0 &&  sel1 && !sel2 && !sel3));
  c_sel2: cover property (@(*) (!sel0 && !sel1 &&  sel2 && !sel3));
  c_sel3: cover property (@(*) (!sel0 && !sel1 && !sel2 &&  sel3));
  c_none: cover property (@(*) (sels==4'b0000));
endmodule

// Bind example:
// bind mux4 mux4_sva #(.DW(DW)) mux4_sva_i (.*);