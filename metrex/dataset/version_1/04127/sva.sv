// SVA for tawas_rcn_master
// Concise checks of request drive, pass-through, response decode, gating, reset, and X safety.
// Bind into DUT.

module tawas_rcn_master_sva #(parameter int MASTER_GROUP_8 = 0)
(
  input  logic              clk,
  input  logic              rst,

  // DUT IO
  input  logic [68:0]       rcn_in,
  input  logic [68:0]       rcn_out,
  input  logic              cs,
  input  logic              wr,
  input  logic [3:0]        mask,
  input  logic [4:0]        seq,
  input  logic [23:0]       addr,
  input  logic [31:0]       wdata,
  input  logic              busy,
  input  logic              rdone,
  input  logic              wdone,
  input  logic [4:0]        rsp_seq,
  input  logic [3:0]        rsp_mask,
  input  logic [23:0]       rsp_addr,
  input  logic [31:0]       rsp_data,

  // Internal regs (sampled by DUT)
  input  logic [68:0]       rin,
  input  logic [68:0]       rout
);

  // Local decodes to mirror DUT
  wire my_resp_sva   = rin[68] && !rin[67] && (rin[65:63] == MASTER_GROUP_8[2:0]);
  wire req_valid_sva = cs && !(rin[68] && !my_resp_sva);
  wire [68:0] req_sva = {1'b1, 1'b1, wr, MASTER_GROUP_8[2:0],
                         seq[4:2], mask, addr[23:2], seq[1:0], wdata};

  // Reset behavior
  assert property (@(posedge clk) rst |-> (rcn_out == 69'd0 && !rdone && !wdone))
    else $error("Reset outputs not cleared");

  // No X on key outputs (after reset released)
  assert property (@(posedge clk) disable iff (rst)
                   !$isunknown({rcn_out, busy, rdone, wdone, rsp_seq, rsp_mask, rsp_addr, rsp_data}))
    else $error("Unknown (X/Z) detected on outputs");

  // Busy definition
  assert property (@(posedge clk) disable iff (rst)
                   busy == (rin[68] && !my_resp_sva))
    else $error("busy mismatch");

  // req_valid gating: never assert when busy
  assert property (@(posedge clk) disable iff (rst)
                   (req_valid_sva |-> !busy))
    else $error("req_valid allowed while busy");

  // Drive rules (next-cycle rout/rcn_out selection)
  // If we requested last cycle, we must drive our req this cycle
  assert property (@(posedge clk) disable iff (rst)
                   $past(req_valid_sva) |-> (rcn_out == $past(req_sva)))
    else $error("Request not driven as expected");

  // If no request last cycle and our response arrived, we must drive zeros (swallow)
  assert property (@(posedge clk) disable iff (rst)
                   ($past(my_resp_sva) && !$past(req_valid_sva)) |-> (rcn_out == 69'd0))
    else $error("Did not zero-out on my_resp");

  // If neither request nor my response last cycle, pass-through last rin
  assert property (@(posedge clk) disable iff (rst)
                   (!$past(req_valid_sva) && !$past(my_resp_sva)) |-> (rcn_out == $past(rin)))
    else $error("Pass-through behavior violated");

  // Response decode and handshakes
  // rdone/wdone mutually exclusive and only when my_resp
  assert property (@(posedge clk) disable iff (rst)
                   !(rdone && wdone))
    else $error("rdone and wdone both asserted");

  assert property (@(posedge clk) disable iff (rst)
                   (rdone == (my_resp_sva && !rin[66])) && (wdone == (my_resp_sva && rin[66])))
    else $error("rdone/wdone decode mismatch");

  // rsp_* fields must match rin when response is for me
  assert property (@(posedge clk) disable iff (rst)
                   my_resp_sva |-> (rsp_seq  == {rin[62:60], rin[33:32]}) &&
                                  (rsp_mask ==  rin[59:56]) &&
                                  (rsp_addr == {rin[55:34], 2'b00}) &&
                                  (rsp_data ==  rin[31:0]))
    else $error("Response field decode mismatch");

  // Sanity: when we drive a request, header must be valid and addressed from our ID
  assert property (@(posedge clk) disable iff (rst)
                   $past(req_valid_sva) |-> (rcn_out[68] && rcn_out[67] &&
                                             (rcn_out[65:63] == MASTER_GROUP_8[2:0]) &&
                                             (rcn_out[66] == $past(wr))))
    else $error("Request header fields incorrect");

  // Coverage
  cover property (@(posedge clk) disable iff (rst) req_valid_sva);                      // A request issued
  cover property (@(posedge clk) disable iff (rst) my_resp_sva && !rin[66]);            // Read response seen
  cover property (@(posedge clk) disable iff (rst) my_resp_sva &&  rin[66]);            // Write response seen
  cover property (@(posedge clk) disable iff (rst) (busy && cs && !req_valid_sva));     // Gated off by busy
  cover property (@(posedge clk) disable iff (rst)
                  (!$past(req_valid_sva) && !$past(my_resp_sva)) && (rcn_out == $past(rin))); // Pass-through

endmodule

bind tawas_rcn_master
  tawas_rcn_master_sva #(.MASTER_GROUP_8(MASTER_GROUP_8)) i_tawas_rcn_master_sva (
    .clk     (clk),
    .rst     (rst),
    .rcn_in  (rcn_in),
    .rcn_out (rcn_out),
    .cs      (cs),
    .wr      (wr),
    .mask    (mask),
    .seq     (seq),
    .addr    (addr),
    .wdata   (wdata),
    .busy    (busy),
    .rdone   (rdone),
    .wdone   (wdone),
    .rsp_seq (rsp_seq),
    .rsp_mask(rsp_mask),
    .rsp_addr(rsp_addr),
    .rsp_data(rsp_data),
    .rin     (rin),
    .rout    (rout)
  );