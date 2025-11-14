// SVA checker for calculator
checker calculator_sva(input [3:0] in1, input [3:0] in2, input op, input [3:0] out);
  // 5-bit arithmetic to observe carry/borrow; out is modulo-16
  logic [4:0] sum5  = {1'b0,in1} + {1'b0,in2};
  logic [4:0] diff5 = {1'b0,in1} - {1'b0,in2};

  // Functional correctness (mask to 4 bits)
  ap_add: assert property (@(*) disable iff ($isunknown({op,in1,in2})))
           (!op) |-> (out == sum5[3:0]);

  ap_sub: assert property (@(*) disable iff ($isunknown({op,in1,in2})))
           ( op) |-> (out == diff5[3:0]);

  // Known-inputs imply known-output (no X/Z propagation)
  ap_no_x_out: assert property (@(*))
               (!$isunknown({op,in1,in2})) |-> !$isunknown(out);

  // Modular inverses (redundant but strong consistency checks)
  ap_add_inverse: assert property (@(*) disable iff ($isunknown({op,in1,in2})))
                   (!op) |-> (((out - in2) & 4'hF) == in1);

  ap_sub_inverse: assert property (@(*) disable iff ($isunknown({op,in1,in2})))
                   ( op) |-> (((out + in2) & 4'hF) == in1);

  // Coverage: ops, overflow/underflow, and key boundaries
  cp_add:          cover property (@(*) !op);
  cp_sub:          cover property (@(*)  op);
  cp_add_carry:    cover property (@(*) (!op) && sum5[4]);           // addition overflow
  cp_sub_borrow:   cover property (@(*) ( op) && (in1 < in2));       // subtraction underflow
  cp_add_zero:     cover property (@(*) (!op) && (in1==0)   && (in2==0));
  cp_add_max:      cover property (@(*) (!op) && (in1==4'hF)&& (in2==4'hF));
  cp_sub_zero_one: cover property (@(*) ( op) && (in1==0)   && (in2==1));
  cp_wraparound:   cover property (@(*) ( op) && (in1==0)   && (in2==4'hF));
endchecker

// Bind to DUT
bind calculator calculator_sva u_calculator_sva(.in1(in1), .in2(in2), .op(op), .out(out));