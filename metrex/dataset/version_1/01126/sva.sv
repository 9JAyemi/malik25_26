// SVA for emesh_if. Bind this to the DUT.
// Focused, high-quality checks and essential coverage.
module emesh_if_sva #(parameter AW=32, PW=2*AW+40) (
  input        cmesh_access_in,
  input [PW-1:0] cmesh_packet_in,
  input        cmesh_ready_in,
  input        rmesh_access_in,
  input [PW-1:0] rmesh_packet_in,
  input        rmesh_ready_in,
  input        xmesh_access_in,
  input [PW-1:0] xmesh_packet_in,
  input        xmesh_ready_in,
  input        emesh_access_in,
  input [PW-1:0] emesh_packet_in,
  input        emesh_ready_in,

  input        cmesh_ready_out,
  input        cmesh_access_out,
  input [PW-1:0] cmesh_packet_out,
  input        rmesh_ready_out,
  input        rmesh_access_out,
  input [PW-1:0] rmesh_packet_out,
  input        xmesh_ready_out,
  input        xmesh_access_out,
  input [PW-1:0] xmesh_packet_out,
  input        emesh_ready_out,
  input        emesh_access_out,
  input [PW-1:0] emesh_packet_out
);

  default clocking cb @(posedge emesh_ready_in); endclocking

  // Shorthand access to DUT internal rr state (exists in emesh_if)
  wire [1:0] rr = round_robin;

  // Combinational equivalence checks (continuous)
  // These directly encode the DUT's assigns.
  always_comb begin
    // Routing and packet replication
    assert (cmesh_access_out == (emesh_access_in &  emesh_packet_in[0]))
      else $error("cmesh_access_out mismatch");
    assert (rmesh_access_out == (emesh_access_in & ~emesh_packet_in[0]))
      else $error("rmesh_access_out mismatch");
    assert (xmesh_access_out == 1'b0)
      else $error("xmesh_access_out must be 0");

    assert (cmesh_packet_out == emesh_packet_in)
      else $error("cmesh_packet_out != emesh_packet_in");
    assert (rmesh_packet_out == emesh_packet_in)
      else $error("rmesh_packet_out != emesh_packet_in");
    assert (xmesh_packet_out == emesh_packet_in)
      else $error("xmesh_packet_out != emesh_packet_in");

    // Combined ready and access
    assert (emesh_ready_out  == (cmesh_ready_in & rmesh_ready_in & xmesh_ready_in))
      else $error("emesh_ready_out mismatch");
    assert (emesh_access_out == (cmesh_access_in & rmesh_access_in & xmesh_access_in))
      else $error("emesh_access_out mismatch");

    // Backpressure logic
    assert (cmesh_ready_out == ~(cmesh_access_in & ~emesh_ready_in))
      else $error("cmesh_ready_out mismatch");
    assert (rmesh_ready_out == ~(rmesh_access_in & (~emesh_ready_in | ~cmesh_ready_in)))
      else $error("rmesh_ready_out mismatch");
    assert (xmesh_ready_out == ~(xmesh_access_in & (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in)))
      else $error("xmesh_ready_out mismatch");

    // Mutual exclusion and X checks
    assert (!(cmesh_access_out & rmesh_access_out))
      else $error("cmesh_access_out and rmesh_access_out both 1");
    assert (!$isunknown({cmesh_ready_out, cmesh_access_out,
                         rmesh_ready_out, rmesh_access_out,
                         xmesh_ready_out, xmesh_access_out,
                         emesh_ready_out, emesh_access_out,
                         emesh_packet_out}))
      else $error("Unknown (X/Z) detected on key outputs");

    // Output packet selection matches rr
    unique case (rr)
      2'b01: assert (emesh_packet_out == cmesh_packet_in)
               else $error("rr=01: emesh_packet_out != cmesh_packet_in");
      2'b10: assert (emesh_packet_out == rmesh_packet_in)
               else $error("rr=10: emesh_packet_out != rmesh_packet_in");
      default: assert (emesh_packet_out == xmesh_packet_in)
               else $error("rr!=01/10: emesh_packet_out != xmesh_packet_in");
    endcase
  end

  // Round-robin state machine updates (sampled on posedge emesh_ready_in)
  // Disable checks while rr is unknown to avoid power-up X noise.
  property rr_update_c;  cmesh_access_in |-> (rr == 2'b01); endproperty
  property rr_update_r; (!cmesh_access_in &&  rmesh_access_in) |-> (rr == 2'b10); endproperty
  property rr_update_x; (!cmesh_access_in && !rmesh_access_in && xmesh_access_in) |-> (rr == 2'b00); endproperty
  property rr_hold;     (!cmesh_access_in && !rmesh_access_in && !xmesh_access_in) |=> $stable(rr); endproperty

  assert property (disable iff ($isunknown(rr)) rr_update_c) else $error("RR update to 01 failed");
  assert property (disable iff ($isunknown(rr)) rr_update_r) else $error("RR update to 10 failed");
  assert property (disable iff ($isunknown(rr)) rr_update_x) else $error("RR update to 00 failed");
  assert property (disable iff ($isunknown(rr)) rr_hold)     else $error("RR hold failed");
  assert property (disable iff ($isunknown(rr)) rr != 2'b11) else $error("RR illegal state 2'b11");

  // Essential coverage
  // Route decision by emesh_packet_in[0]
  cover property (@cb emesh_access_in &&  emesh_packet_in[0]); // cmesh route
  cover property (@cb emesh_access_in && !emesh_packet_in[0]); // rmesh route

  // Access aggregation occurs
  cover property (@cb cmesh_access_in && rmesh_access_in && xmesh_access_in && emesh_access_out);

  // RR states reached and a transition through all destinations
  cover property (@cb rr == 2'b01);
  cover property (@cb rr == 2'b10);
  cover property (@cb rr == 2'b00);
  cover property (@cb (rr==2'b01) ##1 (rr==2'b10) ##1 (rr==2'b00));

  // Backpressure exercised on each output
  cover property (@cb cmesh_access_in && !emesh_ready_in && !cmesh_ready_out);
  cover property (@cb rmesh_access_in && !emesh_ready_in && !rmesh_ready_out);
  cover property (@cb rmesh_access_in &&  emesh_ready_in && !cmesh_ready_in && !rmesh_ready_out);
  cover property (@cb xmesh_access_in && !emesh_ready_in && !xmesh_ready_out);
  cover property (@cb xmesh_access_in &&  emesh_ready_in && !cmesh_access_in && !xmesh_ready_out);
  cover property (@cb xmesh_access_in &&  emesh_ready_in && !rmesh_access_in && !xmesh_ready_out);

endmodule

bind emesh_if emesh_if_sva #(.AW(AW), .PW(PW)) emesh_if_sva_i (.*);