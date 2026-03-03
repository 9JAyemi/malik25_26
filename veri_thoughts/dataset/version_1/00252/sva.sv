// SVA checker + bind for pipelined_xor_gate
module pipelined_xor_gate_sva
(
  input logic clk,
  input logic a, b,
  input logic out,
  input logic a_reg, b_reg
);

  // Track $past validity
  logic past1, past2;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  default clocking cb @(posedge clk); endclocking

  // Pipeline registers capture inputs (when previous inputs are known)
  property p_regs_capture;
    disable iff (!past1)
      !$isunknown($past({a,b})) |-> {a_reg,b_reg} == $past({a,b});
  endproperty
  assert property (p_regs_capture);

  // Out equals prior a_reg ^ b_reg (1-cycle relation)
  property p_out_from_regs;
    disable iff (!past1)
      !$isunknown($past({a_reg,b_reg})) |-> out == $past(a_reg ^ b_reg);
  endproperty
  assert property (p_out_from_regs);

  // End-to-end: out equals inputs from 2 cycles ago
  property p_out_from_inputs;
    disable iff (!past2)
      !$isunknown($past({a,b},2)) |-> out == ($past(a,2) ^ $past(b,2));
  endproperty
  assert property (p_out_from_inputs);

  // Functional coverage: all 4 input combinations propagate through pipeline
  cover property ( (a==0 && b==0) |=> out==0 );
  cover property ( (a==0 && b==1) |=> out==1 );
  cover property ( (a==1 && b==0) |=> out==1 );
  cover property ( (a==1 && b==1) |=> out==0 );

endmodule

bind pipelined_xor_gate pipelined_xor_gate_sva
  (.clk(clk), .a(a), .b(b), .out(out), .a_reg(a_reg), .b_reg(b_reg));