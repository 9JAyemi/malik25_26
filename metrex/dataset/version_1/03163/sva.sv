// SVA for mux4to1 and its mux2to1 submodules

// 2:1 mux checker
module mux2to1_sva (input [3:0] in0, in1, input sel, input [3:0] out);
  // Functional correctness when select is known
  property p_func;
    @(*) !$isunknown(sel) |-> ##0 (out === (sel ? in1 : in0));
  endproperty
  assert property (p_func);

  // Coverage: both selections observed and produce expected output
  cover property (@(*) (sel==1'b0) ##0 (out===in0));
  cover property (@(*) (sel==1'b1) ##0 (out===in1));
endmodule
bind mux2to1 mux2to1_sva (.*);

// 4:1 mux checker
module mux4to1_sva (input [3:0] in0,in1,in2,in3, input [1:0] sel, input [3:0] out);
  // End-to-end correctness for all select values (when select is known)
  property p_e2e;
    @(*) !$isunknown(sel) |-> ##0 (out ===
      (sel==2'b00 ? in0 :
       sel==2'b01 ? in1 :
       sel==2'b10 ? in2 : in3));
  endproperty
  assert property (p_e2e);

  // Structural stage behavior wrt MSB of select
  property p_stage_lo;
    @(*) (!$isunknown(sel)) && (sel[1]==1'b0) |-> ##0 (out === (sel[0] ? in1 : in0));
  endproperty
  assert property (p_stage_lo);

  property p_stage_hi;
    @(*) (!$isunknown(sel)) && (sel[1]==1'b1) |-> ##0 (out === (sel[0] ? in3 : in2));
  endproperty
  assert property (p_stage_hi);

  // Coverage: hit each select and observe corresponding output
  cover property (@(*) (sel==2'b00) ##0 (out===in0));
  cover property (@(*) (sel==2'b01) ##0 (out===in1));
  cover property (@(*) (sel==2'b10) ##0 (out===in2));
  cover property (@(*) (sel==2'b11) ##0 (out===in3));
endmodule
bind mux4to1 mux4to1_sva (.*);