// SVA for binary_counter
module binary_counter_sva (
  input clk,
  input reset,       // active-low in RTL
  input load,
  input [3:0] load_value,
  input [3:0] q,
  input carry_out,
  input led
);
  default clocking cb @ (posedge clk); endclocking

  // Reset behavior (active-low): while reset=0, q must be 5
  assert property (!reset |-> q == 4'h5);

  // Load takes effect next cycle if still out of reset
  assert property ( (reset && load) ##1 reset |-> (q == $past(load_value)) );

  // Increment/rollover when idle (no load) for two consecutive cycles
  assert property ( (reset && !load) ##1 (reset && !load)
                    |-> (q == (($past(q,1)==4'hF) ? 4'h0 : $past(q,1)+1)) );

  // Output relationships
  assert property ( carry_out == (q == 4'hF) );
  assert property ( led == carry_out );

  // Coverage
  cover property ( !reset && q == 4'h5 ); // reset value observed
  cover property ( (reset && load) ##1 (reset && q == $past(load_value)) ); // load used
  cover property ( (reset && !load && q==4'hE)
                   ##1 (reset && !load && q==4'hF)
                   ##1 (reset && !load && q==4'h0) ); // rollover
  cover property ( q==4'hF && carry_out && led ); // carry/LED high at 15
endmodule

bind binary_counter binary_counter_sva bcounter_sva (.*);