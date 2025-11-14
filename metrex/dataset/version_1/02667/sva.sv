// SVA checker for emesh_if. Bind this to the DUT.
// Clockless (combinational) assertions using @(*) for sampling.

module emesh_if_sva #(parameter AW=32, PW=2*AW+40) (
  input        cmesh_access_in,
  input [PW-1:0] cmesh_packet_in,
  input        cmesh_ready_out,
  input        cmesh_access_out,
  input [PW-1:0] cmesh_packet_out,
  input        cmesh_ready_in,

  input        rmesh_access_in,
  input [PW-1:0] rmesh_packet_in,
  input        rmesh_ready_out,
  input        rmesh_access_out,
  input [PW-1:0] rmesh_packet_out,
  input        rmesh_ready_in,

  input        xmesh_access_in,
  input [PW-1:0] xmesh_packet_in,
  input        xmesh_ready_out,
  input        xmesh_access_out,
  input [PW-1:0] xmesh_packet_out,
  input        xmesh_ready_in,

  input        emesh_access_in,
  input [PW-1:0] emesh_packet_in,
  input        emesh_ready_out,
  input        emesh_access_out,
  input [PW-1:0] emesh_packet_out,
  input        emesh_ready_in
);

  default clocking cb @(*); endclocking

  // Access out encodings
  a_cmesh_access_out: assert property (cmesh_access_out == (emesh_access_in &  emesh_packet_in[0]));
  a_rmesh_access_out: assert property (rmesh_access_out == (emesh_access_in & ~emesh_packet_in[0]));
  a_xmesh_access_out: assert property (xmesh_access_out == 1'b0);

  // Packet mirroring to mesh domains
  a_cmesh_pkt_out:    assert property (cmesh_packet_out == emesh_packet_in);
  a_rmesh_pkt_out:    assert property (rmesh_packet_out == emesh_packet_in);
  a_xmesh_pkt_out:    assert property (xmesh_packet_out == emesh_packet_in);

  // Aggregated ready/access from mesh domains
  a_emesh_ready_out:  assert property (emesh_ready_out  == (cmesh_ready_in & rmesh_ready_in & xmesh_ready_in));
  a_emesh_access_out: assert property (emesh_access_out == (cmesh_access_in & rmesh_access_in & xmesh_access_in));

  // Priority mux for emesh_packet_out
  a_mux_pri_c: assert property ( cmesh_access_in                         |-> (emesh_packet_out == cmesh_packet_in));
  a_mux_pri_r: assert property ((!cmesh_access_in &&  rmesh_access_in)   |-> (emesh_packet_out == rmesh_packet_in));
  a_mux_fall_x:assert property ((!cmesh_access_in && !rmesh_access_in)   |-> (emesh_packet_out == xmesh_packet_in));

  // Ready out equations
  a_cmesh_ready_out: assert property (cmesh_ready_out == ~(cmesh_access_in & ~emesh_ready_in));
  a_rmesh_ready_out: assert property (rmesh_ready_out == ~(rmesh_access_in & (~emesh_ready_in | ~cmesh_ready_in)));
  a_xmesh_ready_out: assert property (xmesh_ready_out == ~(xmesh_access_in & (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in)));

  // Sanity: outputs are known (no X/Z)
  a_no_x_access_outs: assert property (!$isunknown({cmesh_access_out, rmesh_access_out, xmesh_access_out, emesh_access_out}));
  a_no_x_ready_outs:  assert property (!$isunknown({cmesh_ready_out,  rmesh_ready_out,  xmesh_ready_out,  emesh_ready_out}));
  a_no_x_pkts_out:    assert property (!$isunknown({cmesh_packet_out, rmesh_packet_out, xmesh_packet_out, emesh_packet_out}));

  // Key functional coverage
  c_cpath:  cover property (emesh_access_in &&  emesh_packet_in[0] && cmesh_access_out && !rmesh_access_out);
  c_rpath:  cover property (emesh_access_in && !emesh_packet_in[0] && rmesh_access_out && !cmesh_access_out);
  c_mux_c:  cover property ( cmesh_access_in && rmesh_access_in && (emesh_packet_out == cmesh_packet_in));
  c_mux_r:  cover property (!cmesh_access_in && rmesh_access_in && (emesh_packet_out == rmesh_packet_in));
  c_mux_x:  cover property (!cmesh_access_in && !rmesh_access_in && (emesh_packet_out == xmesh_packet_in));

  c_ready_all_hi: cover property (cmesh_ready_in && rmesh_ready_in && xmesh_ready_in && emesh_ready_out);
  c_ready_block_c: cover property (cmesh_access_in && !emesh_ready_in && !cmesh_ready_out);
  c_ready_block_r: cover property (rmesh_access_in && (!emesh_ready_in || !cmesh_ready_in) && !rmesh_ready_out);
  c_ready_block_x: cover property (xmesh_access_in && (!emesh_ready_in || !cmesh_access_in || !rmesh_access_in) && !xmesh_ready_out);

endmodule

// Bind into DUT (tooling permitting wildcard connections). Adjust if your tool dislikes .* in bind.
bind emesh_if emesh_if_sva #(.AW(AW), .PW(PW)) emesh_if_sva_i (.*);