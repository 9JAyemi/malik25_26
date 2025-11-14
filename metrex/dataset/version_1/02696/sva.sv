// SVA for shift_register
module shift_register_sva (
  input clk,
  input load,
  input shift,
  input [7:0] in,
  input [7:0] out
);
  default clocking @(posedge clk); endclocking

  // Load wins; next out == in
  property p_load;
    logic [7:0] i;
    (load, i = in) |=> out == i;
  endproperty
  assert property (p_load);

  // Shift (only when no load): left shift with zero fill
  property p_shift;
    logic [7:0] o;
    (!load && shift, o = out) |=> out == {o[6:0], 1'b0};
  endproperty
  assert property (p_shift);

  // Hold value when idle
  property p_hold;
    logic [7:0] o;
    (!load && !shift, o = out) |=> out == o;
  endproperty
  assert property (p_hold);

  // Explicit zero-fill on shift
  assert property ((!load && shift) |=> out[0] == 1'b0);

  // Priority check when both asserted
  property p_priority;
    logic [7:0] i;
    (load && shift, i = in) |=> out == i;
  endproperty
  assert property (p_priority);

  // Out changes only if a control was asserted
  property p_only_changes_when_ctrl;
    logic [7:0] o; bit l, s;
    (1, o = out, l = load, s = shift) |=> (out != o) |-> (l || s);
  endproperty
  assert property (p_only_changes_when_ctrl);

  // X-propagation sanity
  assert property ((load && !$isunknown(in)) |=> !$isunknown(out));
  assert property ((!load && shift && !$isunknown(out)) |=> !$isunknown(out));

  // Functional coverage
  cover property (load);
  cover property (shift && !load);
  cover property (!shift && !load);
  cover property (load && shift);
  cover property (load ##1 shift ##1 shift);
endmodule

bind shift_register shift_register_sva i_shift_register_sva(
  .clk(clk), .load(load), .shift(shift), .in(in), .out(out)
);