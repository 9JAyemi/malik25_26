// SVA for vga_write_iface
// Bind this file to the DUT:
//   bind vga_write_iface vga_write_iface_asserts sva_i(.*);

module vga_write_iface_asserts
(
  input              wb_clk_i,
  input              wb_rst_i,

  input       [16:1] wbs_adr_i,
  input       [ 1:0] wbs_sel_i,
  input       [15:0] wbs_dat_i,
  input              wbs_stb_i,
  input              wbs_ack_o,

  input       [17:1] wbm_adr_o,
  input       [ 1:0] wbm_sel_o,
  input       [15:0] wbm_dat_o,
  input              wbm_stb_o,
  input              wbm_ack_i,

  input              memory_mapping1,
  input       [ 1:0] write_mode,
  input       [ 1:0] raster_op,
  input       [ 7:0] bitmask,
  input       [ 3:0] set_reset,
  input       [ 3:0] enable_set_reset,
  input       [ 3:0] map_mask,

  input       [15:1] offset,
  input       [15:0] bitmask16,
  input       [15:0] dat_mask,
  input              write_en,
  input              cont,

  input       [ 1:0] plane,
  input       [15:0] final_wr0, final_wr1, final_wr2, final_wr3
);

  default clocking cb @(posedge wb_clk_i); endclocking

  // Reset behavior
  assert property (@cb wb_rst_i |-> plane == 2'b00);

  // Plane next-state and hold
  assert property (@cb (!wb_rst_i && cont)  |=> plane == $past(plane)+2'b01);
  assert property (@cb (!wb_rst_i && !cont) |=> plane == $past(plane));

  // Handshake/flow control equalities
  assert property (@cb cont == ((wbm_ack_i | !write_en) & wbs_stb_i));
  assert property (@cb wbm_stb_o == (write_en & wbs_stb_i));
  assert property (@cb wbs_ack_o == ((plane==2'b11) && cont));

  // Basic implications
  assert property (@cb !wbs_stb_i |-> (!wbm_stb_o && !cont && !wbs_ack_o));
  assert property (@cb wbm_stb_o |-> (write_en && wbs_stb_i));
  assert property (@cb !write_en |-> (!wbm_stb_o && (cont == wbs_stb_i)));
  assert property (@cb (write_en && cont) |-> wbm_ack_i);
  assert property (@cb wbs_ack_o |-> wbs_stb_i);

  // Addressing
  assert property (@cb offset == (memory_mapping1 ? {1'b0, wbs_adr_i[14:1]} : wbs_adr_i[15:1]));
  assert property (@cb wbm_adr_o == {offset, plane});

  // Data/sel muxing
  assert property (@cb wbm_sel_o == wbs_sel_i);
  assert property (@cb wbm_dat_o == (plane[1] ? (plane[0] ? final_wr3 : final_wr2)
                                              : (plane[0] ? final_wr1 : final_wr0)));

  // Write enable decoding
  assert property (@cb write_en == (plane==2'b00 ? map_mask[0] :
                                    plane==2'b01 ? map_mask[1] :
                                    plane==2'b10 ? map_mask[2] : map_mask[3]));

  // Sanity on masks
  assert property (@cb bitmask16 == {bitmask, bitmask});
  assert property (@cb dat_mask  == (wbs_dat_i & bitmask16));

  // Progress/handshake: when enabled and acked, plane steps
  assert property (@cb (wbs_stb_i && wbm_stb_o && wbm_ack_i) |=> plane == $past(plane)+2'b01);

  // Coverages

  // Plane walk through 0->1->2->3 with all planes enabled and acks, then ACK to WB
  cover property (@cb disable iff (wb_rst_i)
    (wbs_stb_i && (map_mask==4'hF) && wbm_ack_i && plane==2'd0)
    ##1 (wbm_ack_i && plane==2'd1)
    ##1 (wbm_ack_i && plane==2'd2)
    ##1 (wbm_ack_i && plane==2'd3)
    ##1 wbs_ack_o);

  // Plane-specific write strobes
  cover property (@cb wbm_stb_o && plane==2'd0);
  cover property (@cb wbm_stb_o && plane==2'd1);
  cover property (@cb wbm_stb_o && plane==2'd2);
  cover property (@cb wbm_stb_o && plane==2'd3);

  // Map mask disabled plane skips (cont without stb_o)
  cover property (@cb wbs_stb_i && !write_en && cont && !wbm_stb_o);

  // Address mapping modes exercised
  cover property (@cb memory_mapping1==1'b0 && cont);
  cover property (@cb memory_mapping1==1'b1 && cont);

  // Write mode selections exercised
  cover property (@cb wbm_stb_o && write_mode==2'b00);
  cover property (@cb wbm_stb_o && write_mode==2'b01);
  cover property (@cb wbm_stb_o && write_mode[1]); // 1x -> val1_write path

  // Raster ops exercised
  cover property (@cb wbm_stb_o && raster_op==2'b00);
  cover property (@cb wbm_stb_o && raster_op==2'b01);
  cover property (@cb wbm_stb_o && raster_op==2'b10);
  cover property (@cb wbm_stb_o && raster_op==2'b11);

  // Set/reset enable exercised
  cover property (@cb wbm_stb_o && (enable_set_reset!=4'b0000));
  cover property (@cb wbm_stb_o && (set_reset!=4'b0000));

endmodule