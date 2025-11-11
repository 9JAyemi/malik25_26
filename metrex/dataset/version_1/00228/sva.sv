// SVA checker for emesh_if. Bind this to the DUT and hook up your env clock/reset.
module emesh_if_sva #(parameter AW=32, PW=2*AW+40) (
  input logic clk, rst_n,

  // DUT ports (all as inputs to checker)
  input logic        cmesh_access_in,
  input logic [PW-1:0] cmesh_packet_in,
  input logic        cmesh_wait_in,
  input logic        rmesh_access_in,
  input logic [PW-1:0] rmesh_packet_in,
  input logic        rmesh_wait_in,
  input logic        xmesh_access_in,
  input logic [PW-1:0] xmesh_packet_in,
  input logic        xmesh_wait_in,
  input logic        emesh_access_in,
  input logic [PW-1:0] emesh_packet_in,
  input logic        emesh_wait_in,

  input logic        cmesh_wait_out,
  input logic        cmesh_access_out,
  input logic [PW-1:0] cmesh_packet_out,
  input logic        rmesh_wait_out,
  input logic        rmesh_access_out,
  input logic [PW-1:0] rmesh_packet_out,
  input logic        xmesh_wait_out,
  input logic        xmesh_access_out,
  input logic [PW-1:0] xmesh_packet_out,
  input logic        emesh_wait_out,
  input logic        emesh_access_out,
  input logic [PW-1:0] emesh_packet_out
);

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional equivalences
  assert property (cmesh_access_out == (emesh_access_in &  emesh_packet_in[0]));
  assert property (rmesh_access_out == (emesh_access_in & ~emesh_packet_in[0]));
  assert property (xmesh_access_out == 1'b0);

  assert property (cmesh_packet_out == emesh_packet_in);
  assert property (rmesh_packet_out == emesh_packet_in);
  assert property (xmesh_packet_out == emesh_packet_in);

  assert property (emesh_wait_out   == (cmesh_wait_in | rmesh_wait_in | xmesh_wait_in));
  assert property (emesh_access_out == (cmesh_access_in | rmesh_access_in | xmesh_access_in));

  assert property (emesh_packet_out ==
                   (cmesh_access_in ? cmesh_packet_in :
                    (rmesh_access_in ? rmesh_packet_in : xmesh_packet_in)));

  assert property (cmesh_wait_out == (cmesh_access_in & emesh_wait_in));
  assert property (rmesh_wait_out == (rmesh_access_in & (emesh_wait_in | cmesh_access_in)));
  assert property (xmesh_wait_out == (xmesh_access_in & (emesh_wait_in | cmesh_access_in | rmesh_access_in)));

  // Consistency
  assert property ((cmesh_access_out ^ rmesh_access_out) == emesh_access_in);
  assert property (!(cmesh_access_out & rmesh_access_out));

  // Control X-guard
  assert property (emesh_access_in |-> !$isunknown(emesh_packet_in[0]));

  // Priority behavior of emesh_packet_out
  assert property (cmesh_access_in |-> (emesh_packet_out == cmesh_packet_in));
  assert property (!cmesh_access_in && rmesh_access_in |-> (emesh_packet_out == rmesh_packet_in));
  assert property (!cmesh_access_in && !rmesh_access_in |-> (emesh_packet_out == xmesh_packet_in));

  // Coverage: routing choices
  cover property (emesh_access_in &&  emesh_packet_in[0] && cmesh_access_out && !rmesh_access_out);
  cover property (emesh_access_in && !emesh_packet_in[0] && rmesh_access_out && !cmesh_access_out);

  // Coverage: mux priority under contention and singles
  cover property (cmesh_access_in && rmesh_access_in && xmesh_access_in
                  && emesh_packet_out == cmesh_packet_in);
  cover property (!cmesh_access_in && rmesh_access_in && xmesh_access_in
                  && emesh_packet_out == rmesh_packet_in);
  cover property (!cmesh_access_in && !rmesh_access_in && xmesh_access_in
                  && emesh_packet_out == xmesh_packet_in);

  // Coverage: wait propagation
  cover property (cmesh_wait_in && !rmesh_wait_in && !xmesh_wait_in && emesh_wait_out);
  cover property (!cmesh_wait_in && rmesh_wait_in && !xmesh_wait_in && emesh_wait_out);
  cover property (!cmesh_wait_in && !rmesh_wait_in && xmesh_wait_in && emesh_wait_out);

  // Coverage: per-port backpressure asserts when enabled
  cover property (cmesh_access_in && emesh_wait_in && cmesh_wait_out);
  cover property (rmesh_access_in && (emesh_wait_in || cmesh_access_in) && rmesh_wait_out);
  cover property (xmesh_access_in && (emesh_wait_in || cmesh_access_in || rmesh_access_in) && xmesh_wait_out);

endmodule

// Example bind (connect clk/rst_n from your environment)
// bind emesh_if emesh_if_sva #(.AW(AW), .PW(PW)) u_emesh_if_sva (
//   .clk(tb_clk), .rst_n(tb_rst_n),
//   .cmesh_access_in(cmesh_access_in), .cmesh_packet_in(cmesh_packet_in), .cmesh_wait_in(cmesh_wait_in),
//   .rmesh_access_in(rmesh_access_in), .rmesh_packet_in(rmesh_packet_in), .rmesh_wait_in(rmesh_wait_in),
//   .xmesh_access_in(xmesh_access_in), .xmesh_packet_in(xmesh_packet_in), .xmesh_wait_in(xmesh_wait_in),
//   .emesh_access_in(emesh_access_in), .emesh_packet_in(emesh_packet_in), .emesh_wait_in(emesh_wait_in),
//   .cmesh_wait_out(cmesh_wait_out), .cmesh_access_out(cmesh_access_out), .cmesh_packet_out(cmesh_packet_out),
//   .rmesh_wait_out(rmesh_wait_out), .rmesh_access_out(rmesh_access_out), .rmesh_packet_out(rmesh_packet_out),
//   .xmesh_wait_out(xmesh_wait_out), .xmesh_access_out(xmesh_access_out), .xmesh_packet_out(xmesh_packet_out),
//   .emesh_wait_out(emesh_wait_out), .emesh_access_out(emesh_access_out), .emesh_packet_out(emesh_packet_out)
// );