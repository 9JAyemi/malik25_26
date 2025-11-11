// Bind these SVA into the DUT for internal signal visibility.
bind top_module top_module_sva();

module top_module_sva;

  // Access DUT scope signals directly via bind
  // clk, rst_n, in, pos, write_en, write_addr, write_data, read_en, read_addr,
  // read_data, final_output, gray_code, priority_encoder, ram

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Address range checks (RAM has 8 entries: indices 0..7)
  ap_addr_wr: assert property (write_en |-> write_addr < 8);
  ap_addr_rd: assert property (read_en  |-> read_addr  < 8);

  // Priority encoder combinational correctness
  ap_prienc_comb: assert property (
    priority_encoder == (in[3] ? 2'b11 :
                         in[2] ? 2'b10 :
                         in[1] ? 2'b01 : 2'b00)
  );

  // pos updates to priority_encoder (1-cycle latency)
  ap_pos_update: assert property (pos == $past(priority_encoder));

  // Gray code equals (pos>>1) ^ pos
  ap_gray_func: assert property (gray_code == ((pos >> 1) ^ pos));

  // final_output packs previous gray_code and read_data (both sampled prior cycle)
  ap_final_pack: assert property (final_output == $past({gray_code, read_data}));

  // Read port behavior: 1-cycle latency; holds when read_en=0
  ap_read_latency: assert property (read_en && read_addr < 8 |-> ##1 read_data == $past(ram[read_addr]));
  ap_read_hold:    assert property (!read_en |-> $stable(read_data));

  // Write takes effect in RAM on next cycle
  ap_write_effect: assert property (write_en && write_addr < 8 |-> ##1 ram[$past(write_addr)] == $past(write_data));

  // Same-cycle read & write to same addr returns old RAM content on the read
  ap_rw_samecycle: assert property (write_en && read_en && write_addr == read_addr && write_addr < 8 |-> ##1 read_data == $past(ram[read_addr]));

  // Fresh-after-reset read returns zero until first write to that address
  bit [7:0] wr_seen;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) wr_seen <= '0;
    else if (write_en && write_addr < 8) wr_seen[write_addr] <= 1'b1;
  end
  ap_read_zero_before_write: assert property (read_en && read_addr < 8 && !wr_seen[read_addr] |-> ##1 read_data == 4'b0000);

  // Coverage

  // Cover each priority case (including no bit set)
  cv_pri_3: cover property (in == 4'b1000 ##1 pos == 2'b11);
  cv_pri_2: cover property (in == 4'b0100 ##1 pos == 2'b10);
  cv_pri_1: cover property (in == 4'b0010 ##1 pos == 2'b01);
  cv_pri_0: cover property (in == 4'b0001 ##1 pos == 2'b00);
  cv_pri_none: cover property (in == 4'b0000 ##1 pos == 2'b00);

  // Cover all Gray code values
  cv_gray_00: cover property (gray_code == 2'b00);
  cv_gray_01: cover property (gray_code == 2'b01);
  cv_gray_11: cover property (gray_code == 2'b11);
  cv_gray_10: cover property (gray_code == 2'b10);

  // Cover reads and writes to all valid addresses
  genvar a;
  generate
    for (a = 0; a < 8; a++) begin : CV_ADDRS
      cover property (write_en && write_addr == a[7:0]);
      cover property (read_en  && read_addr  == a[7:0]);
    end
  endgenerate

endmodule