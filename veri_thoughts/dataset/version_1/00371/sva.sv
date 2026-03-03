// SVA for module current
// Bindable, concise, and checks key functionality and coverage

module current_sva #(parameter int imax = 10, parameter int r = 100)
(
  input  logic        ctrl,
  input  logic [7:0]  vref,
  input  logic        isrc,
  input  logic        isnk
);

  // Combinational sampling event
  event comb_clk; always @* -> comb_clk;
  default clocking cb @(comb_clk); endclocking
  default disable iff ($isunknown({ctrl, vref}));

  // Sanity on parameters
  initial begin
    assert (r > 0) else $fatal(1, "r must be > 0");
    assert (imax >= 0) else $fatal(1, "imax must be >= 0");
  end

  // Helper: LSB of quotient (matches 1-bit output truncation in RTL)
  let q0 = (vref / r)[0];

  // Exact functional equivalence to RTL
  ap_isrc_def: assert property (isrc == (ctrl & q0));
  ap_isnk_def: assert property (isnk == ((~ctrl) & q0));

  // Basic invariants
  ap_mut_excl:  assert property (!(isrc & isnk));
  ap_or_match:  assert property ((isrc | isnk) == q0);

  // Outputs known whenever inputs are known
  ap_no_x:      assert property (!$isunknown({isrc, isnk}));

  // Spec/constraint check: computed current must not exceed imax
  ap_imax:      assert property (((vref / r) <= imax));

  // Coverage
  cp_ctrl_rise: cover property ($rose(ctrl));
  cp_ctrl_fall: cover property ($fell(ctrl));

  // Cover all ctrl x q0 combinations
  cp_c1: cover property ( ctrl &&  q0);
  cp_c2: cover property ( ctrl && !q0);
  cp_c3: cover property (!ctrl &&  q0);
  cp_c4: cover property (!ctrl && !q0);

  // Boundary/interesting vref values
  cp_v0:   cover property (vref == 8'h00);
  cp_vr1:  cover property (vref == (r-1));
  cp_vr:   cover property (vref == r[7:0]);
  cp_vmax: cover property (vref == 8'hFF);

  // Observe output activity
  cp_isrc_r: cover property ($rose(isrc));
  cp_isnk_r: cover property ($rose(isnk));

endmodule

// Bind into DUT, inheriting parameter values
bind current current_sva #(.imax(imax), .r(r)) current_sva_i (.*);