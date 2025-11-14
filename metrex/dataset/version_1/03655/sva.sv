// SVA for Multiplexer_AC__parameterized33
// Concise checks + functional coverage. Bind to the DUT.

module Multiplexer_AC__parameterized33_sva
(
  input  logic        ctrl,
  input  logic [0:0]  D0,
  input  logic [0:0]  D1,
  input  logic [0:0]  D2,
  input  logic [0:0]  S,
  input  logic [2:0]  sel  // internal; bound hierarchically below
);

  // Structural: sel must be zero-extended concat of ctrl
  always_comb begin
    assert (sel === {1'b0, ctrl, ctrl})
      else $error("sel must equal {0,ctrl,ctrl}");
    assert (sel inside {3'b000,3'b011})
      else $error("Illegal sel value");
  end

  // Functional mapping (combinational)
  always_comb begin
    assert (!(ctrl === 1'b0) || (S === D0))
      else $error("S must equal D0 when ctrl==0");
    assert (!(ctrl === 1'b1) || (S === 1'b0))
      else $error("S must be 0 when ctrl==1");

    // X-prop: if driving inputs are known, S must be known
    assert (!((ctrl === 1'b0) && !$isunknown(D0)) || !$isunknown(S))
      else $error("S unknown when ctrl==0 and D0 known");
    assert (!(ctrl === 1'b1) || !$isunknown(S))
      else $error("S unknown when ctrl==1");
  end

  // Influence checks
  // When ctrl==0, D0 drives S (any D0 edge should change S)
  property p_d0_drives_s;
    @(posedge D0[0] or negedge D0[0]) (ctrl === 1'b0) |-> $changed(S[0]);
  endproperty
  assert property (p_d0_drives_s)
    else $error("S must follow D0 when ctrl==0");

  // When ctrl==1, S is constant 0 regardless of D1/D2 activity
  property p_d1d2_no_influence_ctrl1;
    @(posedge D1[0] or negedge D1[0] or posedge D2[0] or negedge D2[0])
      (ctrl === 1'b1) |-> !$changed(S[0]);
  endproperty
  assert property (p_d1d2_no_influence_ctrl1)
    else $error("S must not depend on D1/D2 when ctrl==1");

  // Functional coverage
  cover property (@(negedge ctrl) (S === D0));
  cover property (@(posedge ctrl) (S == 1'b0));
  cover (sel == 3'b000);
  cover (sel == 3'b011);
  cover (!ctrl && (S === D0));
  cover ( ctrl && (S == 1'b0));

endmodule

// Bind to DUT; pass internal sel via hierarchical connection
bind Multiplexer_AC__parameterized33
  Multiplexer_AC__parameterized33_sva sva (.*, .sel(sel));