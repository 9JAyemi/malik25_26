// SVA for decoder (bindable checker)
module decoder_sva (
  input logic [2:0] in,
  input logic       enable,
  input logic [7:0] out
);

  // Sample on any input edge
  default clocking cb @(
    posedge enable or negedge enable or
    posedge in[0]  or negedge in[0]  or
    posedge in[1]  or negedge in[1]  or
    posedge in[2]  or negedge in[2]
  ); endclocking

  // Functional equivalence
  assert property ( !enable |-> out == 8'b0 );
  assert property ( enable |-> (out[7:5] == ~in[2:0] && out[4:2] == in[2:0] && out[1:0] == 2'b00) );

  // Internal consistency when enabled
  assert property ( enable |-> (out[7:5] == ~out[4:2]) );

  // Always-zero LSBs
  assert property ( out[1:0] == 2'b00 );

  // No X/Z propagation when inputs are 2-state
  assert property ( !$isunknown({enable,in}) |-> !$isunknown(out) );

  // Basic covers
  cover property ( !enable && out == 8'b0 );
  cover property ( enable && in == 3'b000 );
  cover property ( enable && in == 3'b001 );
  cover property ( enable && in == 3'b010 );
  cover property ( enable && in == 3'b011 );
  cover property ( enable && in == 3'b100 );
  cover property ( enable && in == 3'b101 );
  cover property ( enable && in == 3'b110 );
  cover property ( enable && in == 3'b111 );
  cover property ( !enable ##1 enable ); // enable rise seen
  cover property (  enable ##1 !enable ); // enable fall seen

endmodule

// Bind into DUT
bind decoder decoder_sva decoder_sva_b (.*);