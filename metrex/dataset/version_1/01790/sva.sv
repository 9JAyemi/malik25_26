// SVA for Multiplexer_AC__parameterized133
module Multiplexer_AC__parameterized133_sva (
  input  logic        ctrl,
  input  logic [0:0]  D0,
  input  logic [0:0]  D1,
  input  logic [0:0]  S,
  input  logic [0:0]  wS
);

  // Combinational functional check with 4-state semantics
  always_comb begin
    assert (S === wS)
      else $error("MUX S != internal wS");

    if (!$isunknown(ctrl)) begin
      assert (S === (ctrl ? D0 : D1))
        else $error("MUX mismatch: ctrl=%b D0=%b D1=%b S=%b", ctrl, D0, D1, S);
    end else begin
      if (D0 === D1) begin
        assert (S === D0)
          else $error("ctrl is X and D0==D1: S must equal D0");
      end else begin
        assert ($isunknown(S))
          else $error("ctrl is X and D0!=D1: S must be X");
      end
    end
  end

  // Selected path must propagate in the same timestep
  property p_ctrl_edge_updates;
    @(posedge ctrl or negedge ctrl)
      !$isunknown(ctrl) |-> ##0 (S === (ctrl ? D0 : D1));
  endproperty
  assert property (p_ctrl_edge_updates);

  property p_d0_changes_when_selected;
    @(posedge D0[0] or negedge D0[0])
      (ctrl === 1'b1) |-> ##0 (S === D0);
  endproperty
  assert property (p_d0_changes_when_selected);

  property p_d1_changes_when_selected;
    @(posedge D1[0] or negedge D1[0])
      (ctrl === 1'b0) |-> ##0 (S === D1);
  endproperty
  assert property (p_d1_changes_when_selected);

  // Unselected input must not affect S
  property p_unselected_d0_no_effect;
    @(posedge D0[0] or negedge D0[0])
      (ctrl === 1'b0 && $stable(ctrl) && $stable(D1)) |-> ##0 $stable(S);
  endproperty
  assert property (p_unselected_d0_no_effect);

  property p_unselected_d1_no_effect;
    @(posedge D1[0] or negedge D1[0])
      (ctrl === 1'b1 && $stable(ctrl) && $stable(D0)) |-> ##0 $stable(S);
  endproperty
  assert property (p_unselected_d1_no_effect);

  // Coverage: both select paths and data values
  cover property (@(posedge ctrl)  D0[0]===1'b0 && S===D0);
  cover property (@(posedge ctrl)  D0[0]===1'b1 && S===D0);
  cover property (@(negedge ctrl)  D1[0]===1'b0 && S===D1);
  cover property (@(negedge ctrl)  D1[0]===1'b1 && S===D1);
  cover property (@(posedge D0[0]) ctrl===1'b1 && S===D0);
  cover property (@(posedge D1[0]) ctrl===1'b0 && S===D1);

endmodule

bind Multiplexer_AC__parameterized133 Multiplexer_AC__parameterized133_sva sva_i (.*);