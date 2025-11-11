// SVA for fanout_splitter_stall_free
// Bind example (adjust instance path):
// bind fanout_splitter_stall_free fanout_splitter_stall_free_sva #(.DATA_WIDTH(DATA_WIDTH), .NUM_FANOUTS(NUM_FANOUTS), .INSERT_AND(INSERT_AND), .INSERT_REGISTER(INSERT_REGISTER)) sva (.*);

module fanout_splitter_stall_free_sva #(
  parameter DATA_WIDTH = 32,
  parameter NUM_FANOUTS = 2,
  parameter INSERT_AND = 0,
  parameter INSERT_REGISTER = 0
)(
  input clock, resetn,
  input [DATA_WIDTH-1:0] i_datain,
  input i_datain_valid,
  output reg o_datain_stall,
  output reg [DATA_WIDTH-1:0] o_dataout,
  input [NUM_FANOUTS-1:0] i_dataout_stall,
  output reg [NUM_FANOUTS-1:0] o_dataout_valid
);

generate
if (INSERT_REGISTER) begin : REG_SVA
  // Reset behavior (from RTL)
  assert property (@(posedge clock) !resetn |-> (o_datain_stall==1'b0 && o_dataout_valid=={NUM_FANOUTS{1'b0}}));

  // Registered datapath and stall (1-cycle latency)
  assert property (@(posedge clock) disable iff (!resetn)
                   $past(resetn) |-> (o_dataout == $past(i_datain)));
  assert property (@(posedge clock) disable iff (!resetn)
                   $past(resetn) |-> (o_datain_stall == (|$past(i_dataout_stall))));

  // Registered valid generation
  if (INSERT_AND==0) begin
    assert property (@(posedge clock) disable iff (!resetn)
                     $past(resetn) |-> (o_dataout_valid == {NUM_FANOUTS{$past(i_datain_valid)}}));
  end else begin
    // Uses previous-cycle i_datain_valid and two-cycles-old o_datain_stall (per non-blocking semantics)
    assert property (@(posedge clock) disable iff (!resetn)
                     $past(resetn,2) |-> (o_dataout_valid == {NUM_FANOUTS{ $past(i_datain_valid) & ~ $past(o_datain_stall,2) }}));
  end

  // No X on outputs when out of reset
  assert property (@(posedge clock) disable iff (!resetn)
                   !$isunknown({o_datain_stall, o_dataout_valid, o_dataout}));

  // Coverage
  cover property (@(posedge clock) disable iff (!resetn) (|i_dataout_stall));         // downstream stall seen
  cover property (@(posedge clock) disable iff (!resetn) (&o_dataout_valid));         // all valids high
  if (INSERT_AND) begin
    // Demonstrate gating: past valid with earlier stall yields no valid now
    cover property (@(posedge clock) disable iff (!resetn)
                    $past(resetn,2) && $past(i_datain_valid) && $past(o_datain_stall,2)
                    && (o_dataout_valid=={NUM_FANOUTS{1'b0}}));
  end
end else begin : COMB_SVA
  // Combinational relations (sampled each cycle)
  assert property (@(posedge clock) (o_datain_stall == (|i_dataout_stall)));
  assert property (@(posedge clock) (o_dataout == i_datain));
  if (INSERT_AND==0) begin
    assert property (@(posedge clock) (o_dataout_valid == {NUM_FANOUTS{i_datain_valid}}));
  end else begin
    assert property (@(posedge clock) (o_dataout_valid == {NUM_FANOUTS{ i_datain_valid & ~o_datain_stall }}));
  end

  // No X on outputs
  assert property (@(posedge clock) !$isunknown({o_datain_stall, o_dataout_valid, o_dataout}));

  // Coverage
  cover property (@(posedge clock) (|i_dataout_stall));
  cover property (@(posedge clock) (&o_dataout_valid));
  if (INSERT_AND) begin
    cover property (@(posedge clock) i_datain_valid && (|i_dataout_stall)
                                   && (o_dataout_valid=={NUM_FANOUTS{1'b0}}));
  end
end
endgenerate

endmodule