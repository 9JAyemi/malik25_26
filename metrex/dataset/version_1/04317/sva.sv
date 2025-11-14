// Bind these assertions into the DUT
// bind data_packet_fifo data_packet_fifo_sva #(.DATA_WIDTH(DATA_WIDTH), .PKT_DEPTH(PKT_DEPTH), .NUM_PACKETS(NUM_PACKETS)) sva_i (.*);

module data_packet_fifo_sva #(parameter DATA_WIDTH=32, PKT_DEPTH=128, NUM_PACKETS=4)
(
  input        reset,
  input        clock,

  // DUT I/Os
  input  [31:0] ram_data_in,
  input         write_enable,
  input         read_enable,
  input         pkt_complete,
  input         skip_packet,

  input         have_space,
  input  [31:0] ram_data_out,
  input         pkt_waiting,
  input         isfull,

  input  [1:0]  usb_ram_packet_out,
  input  [1:0]  usb_ram_packet_in,
  input  [6:0]  usb_ram_offset_out,
  input  [6:0]  usb_ram_offset_in,

  // Internal address concatenations from DUT
  input  [6-2+NUM_PACKETS:0] usb_ram_aout,
  input  [6-2+NUM_PACKETS:0] usb_ram_ain
);

  localparam int DEPTH  = PKT_DEPTH*NUM_PACKETS;
  localparam int ADDR_W = $clog2(DEPTH);
  localparam int OFF_W  = $clog2(PKT_DEPTH);
  localparam int PKT_W  = $clog2(NUM_PACKETS);

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  function automatic int unsigned dist(input logic [ADDR_W-1:0] ain, input logic [ADDR_W-1:0] aout);
    dist = (ain >= aout) ? (ain - aout) : (ain + DEPTH - aout);
  endfunction

  // Sanity/shape checks
  assert property (1 |-> (usb_ram_ain < DEPTH && usb_ram_aout < DEPTH));
  assert property (1 |-> ($bits(usb_ram_offset_in)==OFF_W && $bits(usb_ram_offset_out)==OFF_W &&
                          $bits(usb_ram_packet_in)==PKT_W && $bits(usb_ram_packet_out)==PKT_W &&
                          $bits(usb_ram_ain)==ADDR_W && $bits(usb_ram_aout)==ADDR_W));

  // Reset state
  assert property (reset |=> (usb_ram_packet_out==0 && usb_ram_offset_out==0 &&
                              usb_ram_offset_in==0  && usb_ram_packet_in==0  && !isfull));

  // pkt_waiting comb logic equivalent
  assert property (pkt_waiting == ((usb_ram_ain == usb_ram_aout) ? isfull
                                : (dist(usb_ram_ain, usb_ram_aout) >= PKT_DEPTH)));

  // have_space comb logic equivalent (mirrors DUT special-cases)
  assert property (have_space == ((usb_ram_ain == usb_ram_aout) ? ~isfull
                                : (usb_ram_ain > usb_ram_aout)
                                  ? ((usb_ram_ain - usb_ram_aout) <= PKT_DEPTH*(NUM_PACKETS-1))
                                  : ((usb_ram_aout - usb_ram_ain) >= PKT_DEPTH)));

  // Full implies no space and packet(s) waiting
  assert property (isfull |-> (!have_space && pkt_waiting));

  // Read pointer progression
  assert property (read_enable && (usb_ram_offset_out != {OFF_W{1'b1}}) |->
                   ##1 (usb_ram_offset_out == $past(usb_ram_offset_out)+1 &&
                        usb_ram_packet_out == $past(usb_ram_packet_out)));

  // Read packet boundary: wrap offset, bump packet, clear full
  assert property (read_enable && (usb_ram_offset_out == {OFF_W{1'b1}}) |->
                   ##1 (usb_ram_offset_out == '0 &&
                        usb_ram_packet_out == $past(usb_ram_packet_out)+1 &&
                        !isfull));

  // Skip packet: immediate next cycle effects
  assert property (skip_packet |->
                   ##1 (usb_ram_offset_out == '0 &&
                        usb_ram_packet_out == $past(usb_ram_packet_out)+1 &&
                        !isfull));

  // Write pointer progression (pkt_complete has priority)
  assert property (pkt_complete |->
                   ##1 (usb_ram_offset_in == '0 &&
                        usb_ram_packet_in == $past(usb_ram_packet_in)+1));

  assert property (!pkt_complete && write_enable && (usb_ram_offset_in != {OFF_W{1'b1}}) |->
                   ##1 (usb_ram_offset_in == $past(usb_ram_offset_in)+1 &&
                        usb_ram_packet_in == $past(usb_ram_packet_in)));

  // Saturate at end of packet until completion
  assert property (!pkt_complete && write_enable && (usb_ram_offset_in == {OFF_W{1'b1}}) |->
                   ##1 (usb_ram_offset_in == {OFF_W{1'b1}}));

  // isfull set condition on packet completion when next in == out
  assert property (pkt_complete && ((usb_ram_packet_in + 2'b01) == usb_ram_packet_out) |=> isfull);

  // Stability when no enabling event
  assert property (!(read_enable || skip_packet) |=> $stable(usb_ram_offset_out));
  assert property (!(read_enable && (usb_ram_offset_out == {OFF_W{1'b1}}) || skip_packet) |=> $stable(usb_ram_packet_out));
  assert property (!pkt_complete |=> $stable(usb_ram_packet_in));
  assert property (!(write_enable || pkt_complete) |=> $stable(usb_ram_offset_in));

  // Cover: reach full then drain a packet
  cover property (pkt_complete && ((usb_ram_packet_in + 2'b01) == usb_ram_packet_out)
                  ##1 isfull ##[1:$] (read_enable && (usb_ram_offset_out == {OFF_W{1'b1}})) ##1 !isfull);

  // Cover: pointer wraps
  cover property ((read_enable && usb_ram_offset_out == {OFF_W{1'b1}}) ##1 (usb_ram_packet_out == '0));
  cover property (pkt_complete ##1 (usb_ram_packet_in == '0));

  // Cover: write fills to end then complete packet
  cover property ((write_enable && usb_ram_offset_in == (PKT_DEPTH-2)) ##1
                  (write_enable && usb_ram_offset_in == (PKT_DEPTH-1)) ##1
                  pkt_complete ##1 (usb_ram_offset_in == 0));

  // Cover: skip_packet behavior
  cover property (skip_packet ##1 (usb_ram_offset_out==0 && !isfull));
endmodule