// SVA checkers and binds for the provided design

// Top-level checker
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [7:0]  d,
  input logic [7:0]  reg_out,
  input logic [3:0]  counter_out,
  input logic [7:0]  q
);
  default clocking cb @ (posedge clk); endclocking

  // Sum must equal reg_out + zero-extended counter_out (mod 256)
  assert property ( q == ( ({1'b0,reg_out} + {5'b0,counter_out})[7:0] ) );

  // q must be invariant to select toggles when operands are stable
  assert property ( $changed(select) && $stable(reg_out) && $stable(counter_out) |-> q == $past(q) );

  // During reset cycle, output must reflect reset values of submodules
  assert property ( reset |-> q == 8'h34 );

  // No X/Z after reset deassert
  assert property ( disable iff (reset) !$isunknown({select,d,reg_out,counter_out,q}) );

  // Coverage
  cover property ( !reset && select );
  cover property ( !reset && !select );
  cover property ( !reset && $past(counter_out)==4'hF && counter_out==4'h0 );
  cover property ( !reset && ({1'b0,reg_out} + {5'b0,counter_out})[8] ); // overflow carry
endmodule

// Register checker
module reg_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d,
  input logic [7:0]  q
);
  default clocking cb @ (posedge clk); endclocking

  assert property ( reset |-> q == 8'h34 );
  assert property ( disable iff (reset) q == $past(d) );
  assert property ( disable iff (reset) !$isunknown(q) );

  cover property ( reset );
  cover property ( !reset && q == $past(d) );
endmodule

// Counter checker
module counter_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  q
);
  default clocking cb @ (posedge clk); endclocking

  assert property ( reset |-> q == 4'h0 );
  assert property ( disable iff (reset)
                    ($past(q)==4'hF ? q==4'h0 : q == $past(q)+4'h1) );
  assert property ( disable iff (reset) !$isunknown(q) );

  cover property ( !reset && $past(q)==4'hF && q==4'h0 );
endmodule

// Adder checker (clockless: must always compute modulo-8-bit sum)
module adder_module_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] sum
);
  assert property ( sum == 8'(a + b) );
  assert property ( (!$isunknown(a) && !$isunknown(b)) |-> !$isunknown(sum) );

  cover property ( ({1'b0,a} + {1'b0,b})[8] );
endmodule

// Binds
bind top_module      top_module_sva      u_top_module_sva     (.clk(clk), .reset(reset), .select(select), .d(d), .reg_out(reg_out), .counter_out(counter_out), .q(q));
bind reg_module      reg_module_sva      u_reg_module_sva      (.*);
bind counter_module  counter_module_sva  u_counter_module_sva  (.*);
bind adder_module    adder_module_sva    u_adder_module_sva    (.*);