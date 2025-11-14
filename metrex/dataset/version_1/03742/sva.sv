// SVA for add16/top_module
module top_module_sva(
  input logic        clk,
  input logic [31:0] a, b,
  input logic [1:0]  select,
  input logic [31:0] sum,
  input logic [15:0] adder1_out, adder2_out,
  input logic [31:0] mux_out
);
  default clocking cb @(posedge clk); endclocking

  // Helper expressions
  function automatic logic [15:0] lo16_sum(input logic [15:0] x, y);
    lo16_sum = (x + y); // truncation implied
  endfunction
  function automatic logic [15:0] hi16_sum(input logic [15:0] x, y);
    hi16_sum = (x + y); // truncation implied
  endfunction

  // No-X propagation when inputs are known
  assert property ( !$isunknown({a,b,select}) |-> !$isunknown({adder1_out,adder2_out,mux_out,sum}) );

  // Split adders compute correct 16-bit sums
  assert property ( !$isunknown({a,b}) |-> adder1_out == lo16_sum(a[15:0], b[15:0]) );
  assert property ( !$isunknown({a,b}) |-> adder2_out == hi16_sum(a[31:16], b[31:16]) );

  // MUX correctness over all select encodings
  assert property ( select == 2'b00 |-> mux_out == a );
  assert property ( select != 2'b00 |-> mux_out == b );

  // Structural final sum check
  assert property ( sum == {adder2_out, adder1_out} + mux_out );

  // End-to-end check from only primaries
  assert property (
    !$isunknown({a,b,select}) |->
    sum == { hi16_sum(a[31:16], b[31:16]), lo16_sum(a[15:0], b[15:0]) }
           + ((select==2'b00) ? a : b)
  );

  // Coverage: select values and carries in both halves
  cover property ( select == 2'b00 );
  cover property ( select == 2'b01 );
  cover property ( select == 2'b10 );
  cover property ( select == 2'b11 );

  cover property ( ({1'b0,a[15:0]}  + {1'b0,b[15:0]})[16] );       // low 16-bit carry
  cover property ( ({1'b0,a[31:16]} + {1'b0,b[31:16]})[16] );      // high 16-bit carry
  cover property ( ({1'b0,a[15:0]}  + {1'b0,b[15:0]})[16]
                && ({1'b0,a[31:16]} + {1'b0,b[31:16]})[16] );      // both carries
endmodule

bind top_module top_module_sva u_top_module_sva (.*);