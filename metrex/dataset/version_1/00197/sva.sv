// SVA checkers (clockless, sampled on $global_clock) and binds

// Top-level checker
module top_module_sva;
  default clocking cb @($global_clock); endclocking

  wire [3:0] sel_data = (sel==2'b00) ? in0 :
                        (sel==2'b01) ? in1 :
                        (sel==2'b10) ? in2 : in3;

  // Functional equivalence
  assert property (##0 out == sel_data + 4'd3);
  assert property (##0 mux_out == sel_data);
  assert property (##0 adder_out == mux_out + 4'd3);

  // X-propagation safety
  assert property (##0 (!$isunknown({in0,in1,in2,in3,sel})) |-> !$isunknown({mux_out,adder_out,out}));

  // Coverage
  cover property (sel==2'b00);
  cover property (sel==2'b01);
  cover property (sel==2'b10);
  cover property (sel==2'b11);
  cover property (sel==2'b00 ##1 sel==2'b01 ##1 sel==2'b10 ##1 sel==2'b11);
  cover property (##0 (sel_data >= 4'd13) && (out < 4'd3)); // wrap-around by +3
endmodule

bind top_module top_module_sva;


// mux checker
module mux_4to1_sva;
  default clocking cb @($global_clock); endclocking

  // Decode conditions and one-hot check
  wire c3 =  sel[1] &  sel[0];
  wire c2 =  sel[1] & ~sel[0];
  wire c1 = ~sel[1] &  sel[0];
  wire c0 = ~sel[1] & ~sel[0];
  assert property (##0 $onehot({c3,c2,c1,c0}));

  // Functional mapping
  assert property (##0 (sel==2'b00) |-> (out==in0));
  assert property (##0 (sel==2'b01) |-> (out==in1));
  assert property (##0 (sel==2'b10) |-> (out==in2));
  assert property (##0 (sel==2'b11) |-> (out==in3));

  // Gate-level consistency
  assert property (##0 and0_out == (c3 ? in3 : 4'b0));
  assert property (##0 and1_out == (c2 ? in2 : 4'b0));
  assert property (##0 and2_out == (c1 ? in1 : 4'b0));
  assert property (##0 and3_out == (c0 ? in0 : 4'b0));
  assert property (##0 or0_out == (and0_out | and1_out));
  assert property (##0 or1_out == (and2_out | and3_out));
  assert property (##0 out     == (or0_out | or1_out));

  // X-propagation safety
  assert property (##0 (!$isunknown({in0,in1,in2,in3,sel})) |-> !$isunknown(out));

  // Coverage
  cover property (sel==2'b00);
  cover property (sel==2'b01);
  cover property (sel==2'b10);
  cover property (sel==2'b11);
endmodule

bind mux_4to1 mux_4to1_sva;


// adder checker
module binary_adder_sva;
  default clocking cb @($global_clock); endclocking

  // Arithmetic correctness (modulo 16)
  assert property (##0 sum == (a + b));

  // Carry-out (overflow) coverage
  cover property (##0 ({1'b0,a} + {1'b0,b})[4]);

  // X-propagation safety
  assert property (##0 (!$isunknown({a,b})) |-> !$isunknown(sum));
endmodule

bind binary_adder binary_adder_sva;