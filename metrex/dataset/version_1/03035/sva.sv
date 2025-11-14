// SVA for toggle_module
module toggle_module_sva #(parameter WIDTH=8)
(
  input  logic                 clk,
  input  logic                 toggle,
  input  logic [WIDTH-1:0]     cyc_copy,
  input  logic [WIDTH-1:0]     cyc_count,
  input  logic [WIDTH-1:0]     cyc_copy_reg,
  input  logic                 toggle_up
);

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // On toggle=1: reset count, load copy_reg from cyc_copy, toggle_up holds
  property p_load_on_toggle;
    toggle |=> (cyc_count==0 && cyc_copy_reg==$past(cyc_copy) && toggle_up==$past(toggle_up));
  endproperty
  a_load_on_toggle: assert property (p_load_on_toggle);

  // While counting (toggle=0 and no match): count increments, copy_reg tracks cyc_copy, toggle_up holds
  property p_count_up_track_copy;
    (!toggle && (cyc_count != cyc_copy_reg))
      |=> (cyc_count == $past(cyc_count)+1 && cyc_copy_reg==$past(cyc_copy) && toggle_up==$past(toggle_up));
  endproperty
  a_count_up_track_copy: assert property (p_count_up_track_copy);

  // On match with toggle=0: toggle output, reset count, hold copy_reg
  property p_toggle_and_reset_on_match;
    (!toggle && (cyc_count == cyc_copy_reg))
      |=> (toggle_up == !$past(toggle_up) && cyc_count==0 && cyc_copy_reg==$past(cyc_copy_reg));
  endproperty
  a_toggle_and_reset_on_match: assert property (p_toggle_and_reset_on_match);

  // Toggle_up changes only due to the match event, and must invert
  property p_toggle_up_changes_only_on_match;
    $changed(toggle_up) |-> ($past(!toggle && (cyc_count==cyc_copy_reg)) && toggle_up == !$past(toggle_up));
  endproperty
  a_toggle_up_changes_only_on_match: assert property (p_toggle_up_changes_only_on_match);

  // ----------------
  // Functional coverage
  // ----------------

  // Cover a normal toggle event on match
  c_match_toggle: cover property (!toggle && (cyc_count==cyc_copy_reg) |=> $changed(toggle_up));

  // Cover a short count progression then a match
  c_progress_then_match: cover property ((!toggle && (cyc_count!=cyc_copy_reg)) [*3]
                                         ##1 (!toggle && (cyc_count==cyc_copy_reg)));

  // Cover loading via toggle pulse
  c_load_on_toggle: cover property (toggle |=> (cyc_count==0 && cyc_copy_reg==$past(cyc_copy)));

  // Cover extreme cases: zero and max period matches
  c_zero_period: cover property ((!toggle && (cyc_copy_reg==0) && (cyc_count==0)) |=> $changed(toggle_up));
  c_max_period:  cover property ((!toggle && (cyc_copy_reg=={WIDTH{1'b1}}) && (cyc_count=={WIDTH{1'b1}}))
                                 |=> $changed(toggle_up));

endmodule

// Bind into the DUT (exposes internals for checking)
bind toggle_module toggle_module_sva #(.WIDTH(8)) u_toggle_module_sva (
  .clk         (clk),
  .toggle      (toggle),
  .cyc_copy    (cyc_copy),
  .cyc_count   (cyc_count),
  .cyc_copy_reg(cyc_copy_reg),
  .toggle_up   (toggle_up)
);