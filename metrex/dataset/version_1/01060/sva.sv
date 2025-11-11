// SVA checker for mux2to1
module mux2to1_sva (input logic [3:0] in0, in1, input logic ctrl, input logic [3:0] out);

  // Functional correctness for known ctrl
  property p_sel0; @(in0 or in1 or ctrl) (ctrl === 1'b0) |-> (out === in0); endproperty
  property p_sel1; @(in0 or in1 or ctrl) (ctrl === 1'b1) |-> (out === in1); endproperty
  assert property (p_sel0);
  assert property (p_sel1);

  // X/Z control semantics (bit-accurate merge)
  genvar i;
  for (i = 0; i < 4; i++) begin : x_sem
    property p_x_same;
      @(in0 or in1 or ctrl)
      ((ctrl !== 1'b0) && (ctrl !== 1'b1) && (in0[i] === in1[i])) |-> (out[i] === in0[i]);
    endproperty
    property p_x_diff;
      @(in0 or in1 or ctrl)
      ((ctrl !== 1'b0) && (ctrl !== 1'b1) && (in0[i] !== in1[i])) |-> $isunknown(out[i]);
    endproperty
    assert property (p_x_same);
    assert property (p_x_diff);
  end

  // No spurious out changes: out changes only if ctrl or selected input (per ctrl) changes
  property p_no_spurious_out_change;
    @(in0 or in1 or ctrl or out)
    $changed(out) |-> (
      $changed(ctrl) ||
      ((ctrl === 1'b0) && $changed(in0)) ||
      ((ctrl === 1'b1) && $changed(in1)) ||
      ((ctrl !== 1'b0) && (ctrl !== 1'b1) && ($changed(in0) || $changed(in1)))
    );
  endproperty
  assert property (p_no_spurious_out_change);

  // Optional direct equivalence check (concise)
  property p_eq; @(in0 or in1 or ctrl) out === ((ctrl === 1'b0) ? in0 : in1); endproperty
  assert property (p_eq);

  // Coverage
  cover property (@(in0 or in1 or ctrl) (ctrl === 1'b0) && (out === in0));
  cover property (@(in0 or in1 or ctrl) (ctrl === 1'b1) && (out === in1));
  cover property (@(posedge ctrl) 1'b1);
  cover property (@(negedge ctrl) 1'b1);
  for (i = 0; i < 4; i++) begin : cov_x
    cover property (@(in0 or in1 or ctrl)
      (ctrl !== 1'b0) && (ctrl !== 1'b1) && (in0[i] !== in1[i]) && $isunknown(out[i]));
  end
endmodule

// Bind to DUT
bind mux2to1 mux2to1_sva u_mux2to1_sva(.in0(in0), .in1(in1), .ctrl(ctrl), .out(out));