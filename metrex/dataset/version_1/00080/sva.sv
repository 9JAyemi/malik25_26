// SVA for OSERDESE2
// Bind these assertions to the DUT without modifying RTL

module OSERDESE2_sva (
  input  logic        CLK, CLKDIV, RST,
  input  logic        OFB, OQ, SHIFTOUT1, SHIFTOUT2, TBYTEOUT, TFB, TQ,
  input  logic        D1,D2,D3,D4,D5,D6,D7,D8,
  input  logic [7:0]  buffer,
  input  logic [1:0]  clkdiv_sample,
  input  logic [3:0]  even, odd,
  input  logic        load_parallel
);

  // track past valid on negedge CLK for $past usage
  bit negclk_pv; initial negclk_pv = 1'b0;
  always @(negedge CLK) negclk_pv <= 1'b1;

  // Constant outputs must remain 0
  assert property (@(posedge CLK) (OFB==0 && TQ==0 && TBYTEOUT==0 && SHIFTOUT1==0 && SHIFTOUT2==0 && TFB==0));

  // Buffer must capture D inputs on posedge CLKDIV
  assert property (@(posedge CLKDIV) ##0 buffer == {D8,D7,D6,D5,D4,D3,D2,D1});

  // clkdiv_sample shift register behavior on negedge CLK
  assert property (@(negedge CLK) disable iff(!negclk_pv)
                   ##0 clkdiv_sample == { $past(clkdiv_sample[0]), CLKDIV });

  // Parallel load of even/odd nibbles from buffer when load_parallel
  assert property (@(negedge CLK)
                   load_parallel |-> ##0 (even == {buffer[6],buffer[4],buffer[2],buffer[0]} &&
                                           odd  == {buffer[7],buffer[5],buffer[3],buffer[1]}));

  // Shift-right with zero-fill when not loading
  assert property (@(negedge CLK) disable iff(!negclk_pv)
                   !load_parallel |-> ##0 (even == {1'b0, $past(even[3:1])} &&
                                           odd  == {1'b0, $past(odd[3:1])}));

  // OQ must mux correctly between even[0]/odd[0] based on CLK level
  assert property (@(posedge CLK) ##0 OQ == even[0]);
  assert property (@(negedge CLK) ##0 OQ == odd[0]);

  // No X/Z on OQ at clock edges
  assert property (@(posedge CLK) !$isunknown(OQ));
  assert property (@(negedge CLK) !$isunknown(OQ));

  // Coverage
  cover property (@(posedge CLKDIV) 1);                      // buffer sampling
  cover property (@(negedge CLK) load_parallel);            // a load event
  cover property (@(negedge CLK) load_parallel ##1 !load_parallel[*3]); // load then 3 shifts
  // Observe first two serialized bits relative to captured buffer
  cover property (@(negedge CLK) load_parallel ##0 (OQ==buffer[1]) ##1 (OQ==buffer[0]));

endmodule

bind OSERDESE2 OSERDESE2_sva sva_inst (.*);