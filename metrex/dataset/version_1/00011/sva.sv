// SVA for comparator + shift_reg_comp
// Bind-friendly, concise, with key checks and coverage

// Assertions for comparator
module comparator_sva (
  input [3:0] in1,
  input [3:0] in2,
  input       out
);
  // Check functional correctness when inputs are known
  property p_cmp_func;
    @((in1 or in2 or out)) (!$isunknown({in1,in2})) |-> (out == (in1 == in2));
  endproperty
  assert property (p_cmp_func);

  // When any input bit is X/Z, out should go X (matches == semantics)
  property p_cmp_xprop;
    @((in1 or in2 or out)) $isunknown({in1,in2}) |-> $isunknown(out);
  endproperty
  assert property (p_cmp_xprop);

  // Coverage: equal and not-equal cases with known inputs
  cover property (@(in1 or in2) (!$isunknown({in1,in2})) && (in1 == in2));
  cover property (@(in1 or in2) (!$isunknown({in1,in2})) && (in1 != in2));
endmodule

bind comparator comparator_sva u_comparator_sva (
  .in1(in1), .in2(in2), .out(out)
);

// Assertions for shift_reg_comp
module shift_reg_comp_sva (
  input        clk,
  input        reset,
  input        load,
  input        enable,
  input [3:0]  data_in,
  input [3:0]  out,
  input        comp_out
);
  // Reset drives out to zero on the next cycle
  assert property (@(posedge clk) reset |=> (out == 4'b0));

  // On load or enable, out updates with previous-cycle data_in
  assert property (@(posedge clk) (!reset && (load || enable)) |=> (out == $past(data_in)));

  // When idle, out holds its value
  assert property (@(posedge clk) (!reset && !load && !enable) |=> (out == $past(out)));

  // Integration check: comparator output matches equality when known
  assert property (@(posedge clk) (!$isunknown({data_in,out})) |-> (comp_out == (data_in == out)));

  // Optional stronger check: if we just updated and data_in stayed the same, next cycle comp_out must be 1
  assert property (@(posedge clk)
                   (!reset && (load || enable) && (data_in == $past(data_in)) && !$isunknown({data_in,$past(data_in)}))
                   |=> comp_out);

  // Coverage: reset pulse, load, enable, idle, and equality/mismatch cases
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (@(posedge clk) (!reset && load));
  cover property (@(posedge clk) (!reset && enable));
  cover property (@(posedge clk) (!reset && !load && !enable));
  cover property (@(posedge clk) (!reset && !$isunknown({data_in,out}) && (data_in == out)));
  cover property (@(posedge clk) (!reset && !$isunknown({data_in,out}) && (data_in != out)));
endmodule

bind shift_reg_comp shift_reg_comp_sva u_shift_reg_comp_sva (
  .clk(clk), .reset(reset), .load(load), .enable(enable),
  .data_in(data_in), .out(out), .comp_out(comp_out)
);