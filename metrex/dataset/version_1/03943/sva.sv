// SVA for shift_register
module shift_register_sva (
  input logic        clk,
  input logic        d,
  input logic        q,
  input logic [2:0]  reg_data,
  input logic        q_out
);
  default clocking cb @(posedge clk); endclocking

  // Core functional checks
  // 1) 3-bit shift update
  assert property ( !$isunknown({$past(reg_data[1:0]), $past(d)}) |-> 
                    reg_data == {$past(reg_data[1:0]), $past(d)} );

  // 2) Tap to output register (q_out gets prior reg_data[2])
  assert property ( !$isunknown($past(reg_data[2])) |-> 
                    q_out == $past(reg_data[2]) );

  // 3) Continuous assign to q
  assert property ( q == q_out );

  // 4) End-to-end latency: q(t) == d(t-3)
  assert property ( !$isunknown($past(d,3)) |-> 
                    q == $past(d,3) );

  // Coverage: observe 1 and 0 propagating to q after 3 cycles
  cover property ( $rose(d) ##3 q );
  cover property ( $fell(d) ##3 !q );
endmodule

bind shift_register shift_register_sva u_shift_register_sva (
  .clk(clk),
  .d(d),
  .q(q),
  .reg_data(reg_data),
  .q_out(q_out)
);