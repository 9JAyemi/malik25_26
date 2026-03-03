// SVA checker for sky130_fd_sc_ls__inv
module sky130_fd_sc_ls__inv_sva (input logic A, Y);

  // Combinational functional equivalence and X/Z behavior
  always_comb begin
    assert (Y === ~A)
      else $error("INV mismatch: Y=%b, A=%b (expected Y=~A)", Y, A);

    if (!$isunknown(A)) begin
      assert (!$isunknown(Y))
        else $error("INV bad X/Z: A known=%b but Y is X/Z", A);
    end else begin
      assert ($isunknown(Y))
        else $error("INV X-prop: A is X/Z but Y is not X");
    end
  end

  // Edge-based functional checks (non-overlapped to sample post-update)
  property inv_on_rise; @(posedge A) 1 |=> (Y == 1'b0); endproperty
  property inv_on_fall; @(negedge A) 1 |=> (Y == 1'b1); endproperty
  assert property (inv_on_rise);
  assert property (inv_on_fall);

  // Coverage: both polarities and both edges observed
  cover property (inv_on_rise);
  cover property (inv_on_fall);
  cover property (@(posedge A or negedge A or posedge Y or negedge Y) (A===1'b0 && Y===1'b1));
  cover property (@(posedge A or negedge A or posedge Y or negedge Y) (A===1'b1 && Y===1'b0));

  // Coverage: unknown on input leads to unknown on output
  cover property (@(A) $isunknown(A) |=> $isunknown(Y));

endmodule

// Bind into all instances of the inverter
bind sky130_fd_sc_ls__inv sky130_fd_sc_ls__inv_sva inv_sva_i (.A(A), .Y(Y));