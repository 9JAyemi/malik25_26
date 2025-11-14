// SVA checker for mux_2_to_1
module mux_2_to_1_sva (
  input logic a,
  input logic b,
  input logic sel,
  input logic out,
  input logic w1
);

  // Functional correctness (combinational)
  property p_func_eq;
    @(a or b or sel) disable iff ($isunknown({a,b,sel}))
      out == ((~sel & a) | (sel & b));
  endproperty
  assert property (p_func_eq);

  // Internal wire correctness
  property p_w1_eq;
    @(a or sel) disable iff ($isunknown({a,sel}))
      w1 == (~sel & a);
  endproperty
  assert property (p_w1_eq);

  // Out known when inputs known
  property p_out_known_when_inputs_known;
    @(a or b or sel) !$isunknown({a,b,sel}) |-> !$isunknown(out);
  endproperty
  assert property (p_out_known_when_inputs_known);

  // Structural equation using w1
  property p_struct_eq;
    @(b or sel or w1) disable iff ($isunknown({b,sel,w1}))
      out == (w1 | (sel & b));
  endproperty
  assert property (p_struct_eq);

  // Coverage: hit all input combinations
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b000);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b001);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b010);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b011);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b100);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b101);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b110);
  cover property (@(a or b or sel) ! $isunknown({a,b,sel}) && {sel,a,b} == 3'b111);

  // Coverage: select toggles with differing data and out follows
  cover property (@(posedge sel) ! $isunknown({a,b}) && (a != b) ##0 out == b);
  cover property (@(negedge sel) ! $isunknown({a,b}) && (a != b) ##0 out == a);

endmodule

// Bind into DUT (accesses internal w1)
bind mux_2_to_1 mux_2_to_1_sva u_mux_2_to_1_sva (
  .a(a),
  .b(b),
  .sel(sel),
  .out(out),
  .w1(w1)
);