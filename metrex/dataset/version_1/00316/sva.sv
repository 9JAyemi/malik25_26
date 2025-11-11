// SVA for mux: concise, high-quality checks and coverage
module mux_sva #(parameter bit CHECK_NO_X = 0) (
  input logic ctrl,
  input logic D0,
  input logic D1,
  input logic S
);

  // Combinational correctness (4-state aware)
  always_comb begin
    assert (S === (ctrl ? D1 : D0))
      else $error("mux mismatch: S=%b ctrl=%b D1=%b D0=%b", S, ctrl, D1, D0);
    if (CHECK_NO_X) begin
      assert (!$isunknown({ctrl,D0,D1,S}))
        else $error("mux X/Z detected: ctrl=%b D0=%b D1=%b S=%b", ctrl, D0, D1, S);
    end
  end

  // No influence from unselected input (no-glitch on S when select and selected input are stable)
  // If ctrl==1, D0 toggles must not change S
  assert property (@(posedge D0 or negedge D0)
                   (ctrl===1'b1 && $stable({ctrl,D1})) |-> $stable(S))
    else $error("S changed due to unselected D0 while ctrl=1");
  // If ctrl==0, D1 toggles must not change S
  assert property (@(posedge D1 or negedge D1)
                   (ctrl===1'b0 && $stable({ctrl,D0})) |-> $stable(S))
    else $error("S changed due to unselected D1 while ctrl=0");

  // Functional path coverage (both select branches exercised)
  cover property (@(posedge ctrl) S === D1);
  cover property (@(negedge ctrl) S === D0);

  // Data propagation coverage: selected data edges propagate to S
  cover property (@(posedge D0) (ctrl===1'b0) && $changed(S));
  cover property (@(negedge D0) (ctrl===1'b0) && $changed(S));
  cover property (@(posedge D1) (ctrl===1'b1) && $changed(S));
  cover property (@(negedge D1) (ctrl===1'b1) && $changed(S));

endmodule

// Bind into DUT (no DUT edits required)
bind mux mux_sva u_mux_sva(.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));