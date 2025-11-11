// SVA for bcd_counter
// Bind this file alongside the DUT

module bcd_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:1]  ena,
  input logic [15:0] q
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Access DUT internals in bound scope
  // state, count, and parameters exist in DUT
  // If your tool requires, you can alias: wire [1:0] s = state; wire [15:0] c = count;

  // Basic sanity/consistency
  assert property ( !$isunknown({state, count, ena, q}) );
  assert property ( ena == {state[1], state[0], 1'b1} );
  assert property ( q == count );
  assert property ( state inside {2'b00,2'b01,2'b10,2'b11} );

  // Synchronous reset effect (next cycle)
  assert property ( reset |=> (state==2'b00 && count==16'd0 && q==16'd0 && ena==3'b001) );

  // IDLE behavior: next cycle go to INC_D1; count forced to 0
  assert property ( state==2'b00 |=> (state==2'b01) );
  assert property ( state==2'b00 |=> (count==16'd0) );

  // Count increments exactly by +1 in all INC states
  assert property ( (state inside {2'b01,2'b10,2'b11}) |=> count == $past(count)+16'd1 );

  // INC_D1 transitions/stay conditions
  assert property ( (state==2'b01 && count[3:0]!=4'd10) |=> state==2'b01 );
  assert property ( (state==2'b01 && count[3:0]==4'd10) |=> state==2'b10 );

  // INC_D2 transitions/stay conditions
  assert property ( (state==2'b10 && count[7:4]!=4'd10) |=> state==2'b10 );
  assert property ( (state==2'b10 && count[7:4]==4'd10) |=> state==2'b11 );

  // INC_D3 transitions/stay conditions
  assert property ( (state==2'b11 && count[11:8]!=4'd10) |=> state==2'b11 );
  assert property ( (state==2'b11 && count[11:8]==4'd10) |=> state==2'b00 );

  // Optional spec check: BCD nibbles should never exceed 9 (will flag current RTL)
  assert property ( q[3:0]  <= 4'd9 );
  assert property ( q[7:4]  <= 4'd9 );
  assert property ( q[11:8] <= 4'd9 );
  assert property ( q[15:12]<= 4'd9 );

  // Coverage: visit all states and full cycle through the FSM
  cover property ( state==2'b00 ##1 state==2'b01 ##[1:$] state==2'b10 ##[1:$] state==2'b11 ##1 state==2'b00 );
  cover property ( state==2'b01 && count[3:0]==4'd10 );
  cover property ( state==2'b10 && count[7:4]==4'd10 );
  cover property ( state==2'b11 && count[11:8]==4'd10 );

  // Coverage: observe all enable patterns
  cover property ( ena==3'b001 );
  cover property ( ena==3'b011 );
  cover property ( ena==3'b101 );
  cover property ( ena==3'b111 );
endmodule

bind bcd_counter bcd_counter_sva sva_i (.clk(clk), .reset(reset), .ena(ena), .q(q));