// SVA for top_module
checker top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  input_data,
  input logic        control,
  input logic [2:0]  counter,      // internal
  input logic [2:0]  counter_out,
  input logic [2:0]  xor_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior (synchronous)
  assert property (reset |=> (counter==3'b000 && counter_out==3'b000 && xor_out==3'b000));

  // No X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({control,input_data,counter,counter_out,xor_out}));

  // Counter: increment and wrap
  assert property (disable iff (reset) ($past(counter)!=3'b111) |-> counter == $past(counter)+3'b001);
  assert property (disable iff (reset) ($past(counter)==3'b111) |-> counter == 3'b000);

  // counter_out behavior: follow on control==0, hold on control==1
  assert property (disable iff (reset) ($past(control)==1'b0) |-> counter_out == $past(counter));
  assert property (disable iff (reset) ($past(control)==1'b1) |-> counter_out == $past(counter_out));

  // xor_out behavior: select correct source and XOR with input_data
  assert property (disable iff (reset) ($past(control)==1'b0) |-> xor_out == ($past(counter)     ^ $past(input_data)));
  assert property (disable iff (reset) ($past(control)==1'b1) |-> xor_out == ($past(counter_out) ^ $past(input_data)));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (disable iff (reset) (counter==3'b111) ##1 (counter==3'b000));
  cover property (disable iff (reset) $past(control)==1'b0 && xor_out==($past(counter)^$past(input_data)));
  cover property (disable iff (reset) $past(control)==1'b1 && xor_out==($past(counter_out)^$past(input_data)));
  cover property (disable iff (reset) control ##1 !control ##1 control);
endchecker

// Bind into DUT (connects internal 'counter' as well)
bind top_module top_module_sva sva_i (.*);