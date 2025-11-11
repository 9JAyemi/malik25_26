// Bindable SVA for priority_encoder_mux
module priority_encoder_mux_sva (
  input logic        clk,
  input logic        a,
  input logic        b,
  input logic        sel,
  input logic        out_always,
  input logic [2:0]  pos,
  input logic [2:0]  pos_reg,
  input logic [2:0]  pos_wire
);

  default clocking cb @(posedge clk); endclocking

  // Sel definition must always hold
  assert property ( (pos_wire != 3'd0) == sel );

  // On each clock, out_always selects using the encoder result from the previous cycle
  assert property ( disable iff ($initstate)
                    out_always == ( ($past(pos_wire) != 3'd0) ? b : a ) );

  // On each clock, pos_reg updates using the encoder result from the previous cycle
  assert property ( disable iff ($initstate)
                    pos_reg == ( ($past(pos_wire) != 3'd0) ? $past(pos_wire) : 3'd0 ) );

  // pos must reflect pos_reg (combinational mirror)
  assert property ( disable iff ($initstate) pos == pos_reg );

  // Encoder output range observed at the mux
  assert property ( pos_wire inside {3'd0,3'd1,3'd2} );

  // Coverage: exercise both select paths and encoded positions
  cover property ( disable iff ($initstate) ($past(pos_wire) != 3'd0) && (out_always == b) );
  cover property ( disable iff ($initstate) ($past(pos_wire) == 3'd0) && (out_always == a) );
  cover property ( disable iff ($initstate) pos == 3'd1 );
  cover property ( disable iff ($initstate) pos == 3'd2 );

endmodule

bind priority_encoder_mux priority_encoder_mux_sva mux_sva_i (
  .clk(clk),
  .a(a),
  .b(b),
  .sel(sel),
  .out_always(out_always),
  .pos(pos),
  .pos_reg(pos_reg),
  .pos_wire(pos_wire)
);


// Bindable SVA for priority_encoder (combinational correctness and priority)
module priority_encoder_sva (
  input logic [7:0] in,
  input logic [2:0] out
);

  // Output restricted to implemented codes
  assert property ( out inside {3'd0,3'd1,3'd2} );

  // Priority and mapping (forward)
  assert property ( in[7]                          |-> out == 3'd2 );
  assert property ( !in[7] && in[6]               |-> out == 3'd1 );
  assert property ( !in[7] && !in[6] && in[5]     |-> out == 3'd0 );
  assert property ( !in[7] && !in[6] && !in[5]    |-> out == 3'd0 );

  // Priority (reverse where unambiguous)
  assert property ( out == 3'd2 |-> in[7] );
  assert property ( out == 3'd1 |-> !in[7] && in[6] );

  // Coverage of all cases
  cover property ( in[7] );
  cover property ( !in[7] && in[6] );
  cover property ( !in[7] && !in[6] && in[5] );
  cover property ( !in[7] && !in[6] && !in[5] );

endmodule

bind priority_encoder priority_encoder_sva pe_sva_i (
  .in(in),
  .out(out)
);