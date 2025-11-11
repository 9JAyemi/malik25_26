// SVA for queue_8x9
// Bind this file to the DUT:  bind queue_8x9 queue_8x9_sva sva(.clk, .reset, .nchar, .lchar, .char_i, .stb_i, .ack_o, .dat_o, .full_o, .empty_o, .occupied_tb, .rp_tb, .wp_tb, .we_tb);

module queue_8x9_sva(
  input  logic        clk,
  input  logic        reset,
  input  logic        nchar,
  input  logic        lchar,
  input  logic [7:0]  char_i,
  input  logic        stb_i,
  input  logic        ack_o,
  input  logic [8:0]  dat_o,
  input  logic        full_o,
  input  logic        empty_o,
  input  logic [7:0]  occupied_tb,
  input  logic [2:0]  rp_tb,
  input  logic [2:0]  wp_tb,
  input  logic        we_tb
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Local recomputation of internal conditions
  let eop      = ((char_i[1:0]==2'b01) || (char_i[1:0]==2'b10));
  let ptrs_eq  = (wp_tb == rp_tb);
  let set_occ  = (!ack_o && we_tb && !occupied_tb[wp_tb]);
  let rwc      = (ack_o && we_tb && ptrs_eq); // read/write concurrently on same slot
  let store    = (set_occ || rwc);
  let pop      = (ack_o && occupied_tb[rp_tb]);

  // Reset behavior (synchronous in DUT)
  assert property (reset |-> (!ack_o && occupied_tb==8'h00 && rp_tb==3'd0 && wp_tb==3'd0));

  // Ack behavior
  assert property (ack_o == stb_i);

  // Write enable decoding
  assert property (we_tb == (nchar || (lchar && eop)));

  // Flag-to-state consistency
  assert property (full_o  == occupied_tb[wp_tb]);
  assert property (empty_o == ~occupied_tb[rp_tb]);

  // Pointer updates
  assert property (store |=> wp_tb == $past(wp_tb) + 3'd1);
  assert property (!store |=> wp_tb == $past(wp_tb));
  assert property (pop   |=> rp_tb == $past(rp_tb) + 3'd1);
  assert property (!pop  |=> rp_tb == $past(rp_tb));

  // Occupancy bit updates
  assert property (set_occ           |=> occupied_tb[$past(wp_tb)] == 1'b1);
  assert property (pop && !rwc       |=> occupied_tb[$past(rp_tb)] == 1'b0);
  assert property (rwc               |=> occupied_tb == $past(occupied_tb));

  // Safety: cannot advance wp when trying to write into an occupied slot without concurrent read
  assert property (!ack_o && we_tb && occupied_tb[wp_tb] |=> wp_tb == $past(wp_tb));

  // Safety: cannot advance rp when reading an empty slot
  assert property (ack_o && !occupied_tb[rp_tb] |=> rp_tb == $past(rp_tb));

  // Coverage
  cover property (set_occ);                     // pure write
  cover property (pop);                         // pure read
  cover property (rwc);                         // concurrent read/write same slot
  cover property ($past(wp_tb)==3'd7 && store ##1 (wp_tb==3'd0)); // wp wrap
  cover property ($past(rp_tb)==3'd7 && pop   ##1 (rp_tb==3'd0)); // rp wrap
  cover property (full_o);
  cover property (empty_o);

endmodule