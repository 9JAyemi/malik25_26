// SVA for emesh_if. Bind this module to emesh_if and provide clk/rst_n.
module emesh_if_sva #(parameter AW=32, PW=2*AW+40) (
  input logic clk, rst_n,

  input  logic         cmesh_access_in,
  input  logic [PW-1:0] cmesh_packet_in,
  input  logic         cmesh_ready_in,
  input  logic         rmesh_access_in,
  input  logic [PW-1:0] rmesh_packet_in,
  input  logic         rmesh_ready_in,
  input  logic         xmesh_access_in,
  input  logic [PW-1:0] xmesh_packet_in,
  input  logic         xmesh_ready_in,
  input  logic         emesh_access_in,
  input  logic [PW-1:0] emesh_packet_in,
  input  logic         emesh_ready_in,

  input  logic         cmesh_ready_out,
  input  logic         cmesh_access_out,
  input  logic [PW-1:0] cmesh_packet_out,
  input  logic         rmesh_ready_out,
  input  logic         rmesh_access_out,
  input  logic [PW-1:0] rmesh_packet_out,
  input  logic         xmesh_ready_out,
  input  logic         xmesh_access_out,
  input  logic [PW-1:0] xmesh_packet_out,
  input  logic         emesh_ready_out,
  input  logic         emesh_access_out,
  input  logic [PW-1:0] emesh_packet_out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Decode to C/R meshes
  a_cmesh_access: assert property (cmesh_access_out == (emesh_access_in & emesh_packet_in[0]));
  a_rmesh_access: assert property (rmesh_access_out == (emesh_access_in & ~emesh_packet_in[0]));
  a_access_excl:  assert property (!(cmesh_access_out && rmesh_access_out));
  a_access_part:  assert property ((cmesh_access_out ^ rmesh_access_out) == emesh_access_in);
  a_xmesh_access0:assert property (xmesh_access_out == 1'b0);

  // Packet fanout to meshes
  a_cmesh_pkt:    assert property (cmesh_packet_out == emesh_packet_in);
  a_rmesh_pkt:    assert property (rmesh_packet_out == emesh_packet_in);
  a_xmesh_pkt:    assert property (xmesh_packet_out == emesh_packet_in);

  // Aggregation from meshes
  a_emesh_ready:  assert property (emesh_ready_out == (cmesh_ready_in & rmesh_ready_in & xmesh_ready_in));
  a_emesh_access: assert property (emesh_access_out == (cmesh_access_in & rmesh_access_in & xmesh_access_in));

  // Output packet select priority C > R > X
  a_sel_c:        assert property ( cmesh_access_in                           |-> (emesh_packet_out == cmesh_packet_in));
  a_sel_r:        assert property ((!cmesh_access_in &&  rmesh_access_in)     |-> (emesh_packet_out == rmesh_packet_in));
  a_sel_x:        assert property ((!cmesh_access_in && !rmesh_access_in)     |-> (emesh_packet_out == xmesh_packet_in));

  // Ready backpressure logic
  a_c_ready:      assert property (cmesh_ready_out == ~(cmesh_access_in & ~emesh_ready_in));
  a_r_ready:      assert property (rmesh_ready_out == ~(rmesh_access_in & (~emesh_ready_in | ~cmesh_ready_in)));
  a_x_ready:      assert property (xmesh_ready_out == ~(xmesh_access_in & (~emesh_ready_in | ~cmesh_access_in | ~rmesh_access_in)));

  // Sanity implications for backpressure
  a_c_blk:        assert property (cmesh_access_in && !emesh_ready_in                                   |-> !cmesh_ready_out);
  a_r_blk:        assert property (rmesh_access_in && (!emesh_ready_in || !cmesh_ready_in)              |-> !rmesh_ready_out);
  a_x_blk:        assert property (xmesh_access_in && (!emesh_ready_in || !cmesh_access_in || !rmesh_access_in) |-> !xmesh_ready_out);

  // Functional coverage
  c_dec_c:        cover property (emesh_access_in &&  emesh_packet_in[0] && cmesh_access_out);
  c_dec_r:        cover property (emesh_access_in && !emesh_packet_in[0] && rmesh_access_out);

  c_sel_c:        cover property ( cmesh_access_in                           && (emesh_packet_out == cmesh_packet_in));
  c_sel_r:        cover property ((!cmesh_access_in &&  rmesh_access_in)     && (emesh_packet_out == rmesh_packet_in));
  c_sel_x:        cover property ((!cmesh_access_in && !rmesh_access_in)     && (emesh_packet_out == xmesh_packet_in));

  c_ready_all:    cover property (cmesh_ready_in && rmesh_ready_in && xmesh_ready_in && emesh_ready_out);
  c_c_backpress:  cover property (cmesh_access_in && !emesh_ready_in && !cmesh_ready_out);
  c_r_backpress:  cover property (rmesh_access_in && (!emesh_ready_in || !cmesh_ready_in) && !rmesh_ready_out);
  c_x_backpress:  cover property (xmesh_access_in && (!emesh_ready_in || !cmesh_access_in || !rmesh_access_in) && !xmesh_ready_out);

endmodule

// Example bind (provide your clock/reset):
// bind emesh_if emesh_if_sva #(.AW(AW), .PW(PW)) u_emesh_if_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));