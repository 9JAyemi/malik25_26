// SVA for the provided design. Bind this file after compiling the DUT.

module sva_not_gate (input in, input out);
  // Functional check (ignore unknown inputs)
  ap_func: assert property ( !$isunknown(in) |-> out === ~in );
  // Coverage
  cp_in0:  cover property ( in==1'b0 );
  cp_in1:  cover property ( in==1'b1 );
endmodule
bind not_gate sva_not_gate not_gate_sva (.*);

module sva_and_gate (input a, input b, input out);
  ap_func: assert property ( !$isunknown({a,b}) |-> out === (a & b) );
  cp00: cover property ( a==0 && b==0 );
  cp01: cover property ( a==0 && b==1 );
  cp10: cover property ( a==1 && b==0 );
  cp11: cover property ( a==1 && b==1 );
endmodule
bind and_gate sva_and_gate and_gate_sva (.*);

module sva_nor_gate (input a, input b, input out);
  ap_func: assert property ( !$isunknown({a,b}) |-> out === ~(a | b) );
  cp00: cover property ( a==0 && b==0 );
  cp01: cover property ( a==0 && b==1 );
  cp10: cover property ( a==1 && b==0 );
  cp11: cover property ( a==1 && b==1 );
endmodule
bind nor_gate sva_nor_gate nor_gate_sva (.*);

module sva_nor_gate_level (input a, input b, input out);
  ap_func: assert property ( !$isunknown({a,b}) |-> out === ~(a | b) );
  cp00: cover property ( a==0 && b==0 );
  cp01: cover property ( a==0 && b==1 );
  cp10: cover property ( a==1 && b==0 );
  cp11: cover property ( a==1 && b==1 );
endmodule
bind nor_gate_level sva_nor_gate_level nor_gate_level_sva (.*);

module sva_shift_register (input clk, input rst, input data, input [2:0] out);
  // Async reset drives zero immediately
  p_async:        assert property ( @(negedge rst) out == 3'b000 );
  // Hold zero while in reset at clock edges
  p_hold_in_rst:  assert property ( @(posedge clk) !rst |-> out == 3'b000 );
  // Shift behavior (after at least one cycle out of reset)
  p_shift:        assert property ( @(posedge clk) disable iff (!rst)
                                    $past(rst) |-> out == { $past(out[1:0]), $past(data) } );
  // Coverage
  c_rst_assert:   cover property ( @(negedge rst) 1'b1 );
  c_rst_deassert: cover property ( @(posedge rst) 1'b1 );
  c_seq_101:      cover property ( @(posedge clk) disable iff (!rst)
                                   (data==1) ##1 (data==0) ##1 (data==1 && out==3'b101) );
endmodule
bind shift_register sva_shift_register shift_register_sva (.*);

module sva_or_module (input a, input [2:0] b, input out);
  // Cascaded NOR functional equivalence
  ap_chain: assert property ( !$isunknown({a,b})
                              |-> out === ~( ~( ~(a | b[0]) | b[1]) | b[2] ) );
  // Output coverage
  cp_out0: cover property ( out==1'b0 );
  cp_out1: cover property ( out==1'b1 );
endmodule
bind or_module sva_or_module or_module_sva (.*);

module sva_top_module (input a, input b, input clk, input rst, input data, input out, input [2:0] shift_out);
  // End-to-end functional check across top-level wiring
  ap_top_func: assert property ( !$isunknown({a,shift_out})
                                 |-> out === ~( ~( ~(a | shift_out[0]) | shift_out[1]) | shift_out[2] ) );
  // 'b' must not influence output
  ap_b_no_effect: assert property ( @(posedge clk) disable iff (!rst)
                                    (b != $past(b) && $stable(a) && $stable(data) && $stable(shift_out))
                                    |-> out == $past(out) );
  // Output toggle coverage
  cp_out1: cover property ( out==1'b1 );
  cp_out0: cover property ( out==1'b0 );
endmodule
bind top_module sva_top_module top_module_sva (.a(a), .b(b), .clk(clk), .rst(rst), .data(data), .out(out), .shift_out(shift_out));