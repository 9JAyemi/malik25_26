// SVA checker for fourbitmuxcase
module fourbitmuxcase_sva (
  input logic [3:0] in,
  input logic [1:0] s,
  input logic       out
);

  // Functional correctness: when s is known, out matches selected input bit
  property p_mux_map;
    @(in or s or out) (!$isunknown(s)) |-> (out === in[s]);
  endproperty
  assert property (p_mux_map);

  // Default behavior: when s is X/Z, case default forces out to 0
  property p_default_on_xs;
    @(in or s or out) ($isunknown(s)) |-> (out == 1'b0);
  endproperty
  assert property (p_default_on_xs);

  // No spurious X: if s and selected input bit are known, out is known
  property p_no_spurious_x;
    @(in or s or out) (!$isunknown(s) && !$isunknown(in[s])) |-> !$isunknown(out);
  endproperty
  assert property (p_no_spurious_x);

  // Output only changes when inputs (in or s) change
  property p_out_change_has_cause;
    @(out) ($changed(in) || $changed(s));
  endproperty
  assert property (p_out_change_has_cause);

  // Coverage: hit each select value and mapping
  cover property (@(in or s) (s == 2'b00) ##0 (out === in[0]));
  cover property (@(in or s) (s == 2'b01) ##0 (out === in[1]));
  cover property (@(in or s) (s == 2'b10) ##0 (out === in[2]));
  cover property (@(in or s) (s == 2'b11) ##0 (out === in[3]));

  // Coverage: exercise default path when s is X/Z
  cover property (@(in or s) $isunknown(s) ##0 (out == 1'b0));

endmodule

// Bind into DUT
bind fourbitmuxcase fourbitmuxcase_sva u_fourbitmuxcase_sva (.in(in), .s(s), .out(out));