// SVA for and_or_not
// Bindable, concise, and focused on key checks/coverage.

module and_or_not_sva (
    input logic a, b, rsb,
    input logic yi,  // internal reg in DUT; bound by name
    input logic y
);

  // Functional correctness of yi (after NBA update in same timestep)
  property p_yi_func;
    @(a or b or rsb) disable iff ($isunknown({a,b,rsb}))
      1'b1 |-> ##0 (yi === ((~rsb) | (a & b)));
  endproperty
  assert property (p_yi_func);

  // y follows yi with #1 inertial delay (only check if yi stayed stable for the whole delay)
  always @(yi) begin
    automatic logic yi_snapshot = yi;
    #1 if (yi === yi_snapshot) assert (y === yi_snapshot)
         else $error("and_or_not: y did not equal yi after #1 inertial delay");
  end

  // No X on outputs once inputs are known
  property p_no_x_yi;
    @(a or b or rsb or yi) disable iff ($isunknown({a,b,rsb}))
      ##0 !$isunknown(yi);
  endproperty
  assert property (p_no_x_yi);

  property p_no_x_y;
    @(y) !$isunknown(y);
  endproperty
  assert property (p_no_x_y);

  // Functional coverage: all meaningful input cases and resulting yi
  cover property (@(a or b or rsb) rsb==0         ##0 yi==1);
  cover property (@(a or b or rsb) rsb==1 && a&&b ##0 yi==1);
  cover property (@(a or b or rsb) rsb==1 && !a&&!b ##0 yi==0);
  cover property (@(a or b or rsb) rsb==1 && (a^b) ##0 yi==0);

  // Propagation coverage: edges propagate to y after #1 (when not filtered)
  always @(posedge yi) begin #1 if ($rose(y)) cover(1); end
  always @(negedge yi) begin #1 if ($fell(y)) cover(1); end

endmodule

// Bind into the DUT (assumes signal names match, including internal yi)
bind and_or_not and_or_not_sva sva_and_or_not (.*);