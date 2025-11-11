// SVA checker for mux_2to1. Bind to the DUT and provide a sampling clock.
// Example bind:
//   bind mux_2to1 mux_2to1_sva u_mux_sva(.A(A), .B(B), .SEL(SEL), .Y(Y), .clk(tb_clk));

module mux_2to1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic Y,
  input logic clk
);

  // Functional correctness with 4-state semantics
  property p_func_4state;
    @(posedge clk)
      Y === ((SEL === 1'b1) ? B :
             (SEL === 1'b0) ? A :
             ((A === B) ? A : 1'bx));
  endproperty
  assert property (p_func_4state);

  // X/Z on SEL semantics
  property p_sel_x_pass_when_equal;
    @(posedge clk) (SEL !== 1'b0 && SEL !== 1'b1 && (A === B)) |-> (Y === A);
  endproperty
  assert property (p_sel_x_pass_when_equal);

  property p_sel_x_propagates_when_diff;
    @(posedge clk) (SEL !== 1'b0 && SEL !== 1'b1 && (A !== B)) |-> $isunknown(Y);
  endproperty
  assert property (p_sel_x_propagates_when_diff);

  // No spurious output toggles without input activity
  property p_no_spurious_y_change;
    @(posedge clk) !$changed({A,B,SEL}) |-> !$changed(Y);
  endproperty
  assert property (p_no_spurious_y_change);

  // Functional coverage
  cover property (@(posedge clk) (SEL === 1'b0) && (Y === A));
  cover property (@(posedge clk) (SEL === 1'b1) && (Y === B));
  cover property (@(posedge clk) $rose(SEL));
  cover property (@(posedge clk) $fell(SEL));
  cover property (@(posedge clk) (SEL !== 1'b0 && SEL !== 1'b1) && (A !== B) && $isunknown(Y));
  cover property (@(posedge clk) (SEL !== 1'b0 && SEL !== 1'b1) && (A === B) && (Y === A));

  // Optional: purely combinational immediate check (no clock needed)
  always_comb
    assert (Y === ((SEL === 1'b1) ? B :
                   (SEL === 1'b0) ? A :
                   ((A === B) ? A : 1'bx)))
      else $error("mux_2to1 mismatch: Y=%0b A=%0b B=%0b SEL=%0b", Y, A, B, SEL);

endmodule