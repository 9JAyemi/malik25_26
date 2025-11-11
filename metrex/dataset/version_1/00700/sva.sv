// Bind these SVA to the DUT
bind crc_engine crc_engine_sva();

module crc_engine_sva;

  // Use DUT scope signals directly
  default clocking cb @(posedge HCLK); endclocking
  default disable iff (!HRESETn)

  // Basic protocol/handshake
  a_hresp_const:   assert property (HRESP == OK);
  a_sample_bus_eq: assert property (sample_bus == (HREADYOUT && HREADY));
  a_ahb_enable:    assert property (ahb_enable == (htrans_pp == NON_SEQ));

  // Pipeline registers behavior
  a_pipe_hold: assert property (!sample_bus |-> $stable({haddr_pp,hsize_pp,htrans_pp,hwrite_pp,hselx_pp}));
  a_pipe_load: assert property (sample_bus |=> (haddr_pp  == $past(HADDR[4:2]) &&
                                                hsize_pp  == $past(HSIZE) &&
                                                htrans_pp == $past(HTRANS) &&
                                                hwrite_pp == $past(HWRITE) &&
                                                hselx_pp  == $past(HSElx)));
  // Reset state of flops
  always @(posedge HCLK) if (!HRESETn) begin
    assert (hselx_pp == 1'b0);
    assert (crc_cr_ff == RESET_CRC_CR);
  end

  // Decode one-hotness
  a_dec_onehot   : assert ($onehot0({crc_dr_sel,crc_init_sel,crc_idr_sel,crc_poly_sel,crc_cr_sel}));
  a_en_onehot    : assert ($onehot0({buffer_write_en,crc_init_en,crc_idr_en,crc_poly_en,crc_cr_en,buffer_read_en}));

  // Enable implications
  a_buf_wr_impl  : assert property (buffer_write_en |-> (crc_dr_sel   && write_en));
  a_init_en_impl : assert property (crc_init_en     |-> (crc_init_sel && write_en));
  a_idr_en_impl  : assert property (crc_idr_en      |-> (crc_idr_sel  && write_en));
  a_poly_en_impl : assert property (crc_poly_en     |-> (crc_poly_sel && write_en));
  a_cr_en_impl   : assert property (crc_cr_en       |-> (crc_cr_sel   && write_en));
  a_buf_rd_impl  : assert property (buffer_read_en  |-> (crc_dr_sel   && read_en));

  // Read/write exclusivity and NON_SEQ gating
  a_rw_mutex     : assert property (!(write_en && read_en));
  a_wr_nonseq    : assert property (write_en |-> (htrans_pp == NON_SEQ));
  a_rd_nonseq    : assert property (read_en  |-> (htrans_pp == NON_SEQ));
  a_no_en_off_ns : assert property ((htrans_pp != NON_SEQ) |-> !(write_en || read_en));

  // HREADYOUT gating correctness
  a_hreadyout_eq : assert property (HREADYOUT == !((buffer_write_en && buffer_full) ||
                                                   (buffer_read_en  && read_wait)   ||
                                                   (crc_init_en     && reset_pending)));
  a_stall_wr_buf : assert property ((buffer_write_en && buffer_full)     |-> !HREADYOUT);
  a_stall_rd_buf : assert property ((buffer_read_en  && read_wait)       |-> !HREADYOUT);
  a_stall_init   : assert property ((crc_init_en     && reset_pending)   |-> !HREADYOUT);

  // Bus outputs
  a_bus_wr       : assert property (bus_wr == HWDATA);
  a_bus_size_map : assert property (bus_size == hsize_pp[1:0]);

  // CRC_CR read data composition
  a_crc_cr_rd    : assert property (crc_cr_rd == {24'h0, crc_cr_ff[4:0], 3'h0});

  // CRC_CR flop behavior
  a_crc_cr_update: assert property (crc_cr_en |=> (crc_cr_ff == $past({HWDATA[7], HWDATA[6:5], HWDATA[4:3]})));
  a_crc_cr_hold  : assert property (!crc_cr_en |=> $stable(crc_cr_ff));

  // Config outputs mapping
  a_poly_size    : assert property (crc_poly_size == crc_cr_ff[1:0]);
  a_rev_in_type  : assert property (rev_in_type   == crc_cr_ff[3:2]);
  a_rev_out_type : assert property (rev_out_type  == crc_cr_ff[4]);

  // Reset chain pulse mapping
  a_reset_chain  : assert property (reset_chain == (crc_cr_en && HWDATA[0]));

  // HRDATA mux correctness on reads
  a_rd_dr        : assert property ((read_en && crc_dr_sel)   |-> HRDATA == crc_out);
  a_rd_init      : assert property ((read_en && crc_init_sel) |-> HRDATA == crc_init_out);
  a_rd_idr       : assert property ((read_en && crc_idr_sel)  |-> (HRDATA[7:0] == crc_idr_out && HRDATA[31:8] == 24'h0));
  a_rd_pol       : assert property ((read_en && crc_poly_sel) |-> HRDATA == crc_poly_out);
  a_rd_cr        : assert property ((read_en && crc_cr_sel)   |-> HRDATA == crc_cr_rd);

  // Coverage
  cover_wr_dr        : cover property (buffer_write_en);
  cover_wr_init      : cover property (crc_init_en);
  cover_wr_idr       : cover property (crc_idr_en);
  cover_wr_poly      : cover property (crc_poly_en);
  cover_wr_cr        : cover property (crc_cr_en);

  cover_rd_dr        : cover property (buffer_read_en);
  cover_rd_init      : cover property (read_en && crc_init_sel);
  cover_rd_idr       : cover property (read_en && crc_idr_sel);
  cover_rd_poly      : cover property (read_en && crc_poly_sel);
  cover_rd_cr        : cover property (read_en && crc_cr_sel);

  cover_stall_wr_buf : cover property (buffer_write_en && buffer_full     && !HREADYOUT);
  cover_stall_rd_buf : cover property (buffer_read_en  && read_wait       && !HREADYOUT);
  cover_stall_init   : cover property (crc_init_en     && reset_pending   && !HREADYOUT);

  cover_cfg_poly_all : cover property (crc_cr_en && $changed(crc_poly_size));
  cover_cfg_rev_in   : cover property (crc_cr_en && $changed(rev_in_type));
  cover_cfg_rev_out  : cover property (crc_cr_en && $changed(rev_out_type));
  cover_reset_chain  : cover property (reset_chain);

  cover_bus_sizes    : cover property (sample_bus && (hsize_pp inside {3'b000,3'b001,3'b010}));
  cover_sample_hi    : cover property (sample_bus);
  cover_sample_lo    : cover property (!sample_bus);

endmodule