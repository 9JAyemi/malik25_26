// SVA for mux_2to1
// Bind this module to the DUT to check functionality and provide coverage.

module mux_2to1_sva (input logic sel, in0, in1, out);

  // Functional correctness when select is known (0-delay)
  property p_sel0_func;
    @(sel or in0 or in1 or out) (sel === 1'b0) |-> (out === in0);
  endproperty
  property p_sel1_func;
    @(sel or in0 or in1 or out) (sel === 1'b1) |-> (out === in1);
  endproperty
  assert property (p_sel0_func) else $error("mux_2to1: out != in0 when sel==0");
  assert property (p_sel1_func) else $error("mux_2to1: out != in1 when sel==1");

  // Out must be known when the selected input is known
  property p_no_x_sel0;
    @(sel or in0 or in1 or out) (sel === 1'b0 && !$isunknown(in0)) |-> !$isunknown(out);
  endproperty
  property p_no_x_sel1;
    @(sel or in0 or in1 or out) (sel === 1'b1 && !$isunknown(in1)) |-> !$isunknown(out);
  endproperty
  assert property (p_no_x_sel0) else $error("mux_2to1: X/Z on out with sel==0 and in0 known");
  assert property (p_no_x_sel1) else $error("mux_2to1: X/Z on out with sel==1 and in1 known");

  // Output may only change due to a relevant driver change
  property p_out_change_caused;
    @(sel or in0 or in1 or out)
      $changed(out) |-> ( $changed(sel)
                        || (sel === 1'b0 && $changed(in0))
                        || (sel === 1'b1 && $changed(in1)) );
  endproperty
  assert property (p_out_change_caused) else $error("mux_2to1: out changed without cause");

  // Coverage: exercise select both ways and data-path propagation
  cover property (@(sel) $fell(sel) ##0 (out === in0));
  cover property (@(sel) $rose(sel) ##0 (out === in1));
  cover property (@(in0) (sel === 1'b0 && $changed(in0)) ##0 (out === in0));
  cover property (@(in1) (sel === 1'b1 && $changed(in1)) ##0 (out === in1));

endmodule

bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (.sel(sel), .in0(in0), .in1(in1), .out(out));