// SVA checker for vga_converter
// Bind this file to the DUT: bind vga_converter vga_converter_sva sva_inst (.*);

module vga_converter_sva (
  input  logic         clk,
  input  logic [23:0]  data,
  input  logic         blank,
  input  logic         hs,
  input  logic         vs,
  input  logic [7:0]   vga_data,
  input  logic         blank_out,
  input  logic         hs_out,
  input  logic         vs_out,
  input  logic [1:0]   cnt,
  input  logic [23:0]  data_reg,
  input  logic         hs_reg,
  input  logic         hs_reg1,
  input  logic         vs_reg,
  input  logic         blank_reg
);

  // local sync_pulse (matches DUT wire)
  logic sync_pulse;
  assign sync_pulse = (hs_reg & !hs_reg1);

  // clocking and $past guard
  default clocking cb @(posedge clk); endclocking
  bit past_valid; initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // 1) Input pipeline staging checks
  assert property (hs_reg   == $past(hs));
  assert property (hs_reg1  == $past(hs_reg));
  assert property (vs_reg   == $past(vs));
  assert property (blank_reg== $past(blank));

  // 2) Counter behavior
  // on sync_pulse -> next cnt = 3
  assert property (sync_pulse |=> cnt == 2'b11);
  // no sync: cnt==2 -> next 0
  assert property (!sync_pulse && $past(cnt)==2 |=> cnt==2'b00);
  // no sync: otherwise increment (wraps 3->0)
  assert property (!sync_pulse && $past(cnt)!=2 |=> cnt == ($past(cnt)+2'b01));
  // cnt is always a 2-bit legal value (no X/Z)
  assert property (!$isunknown(cnt) && (cnt inside {[2'b00:2'b11]}));

  // 3) data_reg write/hold protocol
  assert property ((cnt==2'b11) |=> data_reg == $past(data));       // write when cnt==3
  assert property ((cnt!=2'b11) |=> data_reg == $past(data_reg));   // hold otherwise

  // 4) Output functions
  assert property (vga_data == (cnt[1] ? data_reg[23:16]
                                    : (cnt[0] ? data_reg[15:8]
                                              : data_reg[7:0])));
  assert property (blank_out == (blank_reg && (cnt != 2'b00)));
  assert property (hs_out    == (hs_reg    && (cnt != 2'b00)));
  assert property (vs_out    == (vs_reg    && (cnt != 2'b00)));

  // 5) Minimal safety: outputs not X
  assert property (!$isunknown({vga_data, blank_out, hs_out, vs_out}));

  // 6) Key functional coverage
  // cover a full post-sync counter walk (no new syncs assumed over 4 cycles)
  cover property (sync_pulse |=> (cnt==2'b11) ##1 (cnt==2'b00) ##1 (cnt==2'b01) ##1 (cnt==2'b10));
  // cover each vga_data slice usage
  cover property (cnt==2'b00 && vga_data == data_reg[7:0]);
  cover property (cnt==2'b01 && vga_data == data_reg[15:8]);
  cover property (cnt==2'b10 && vga_data == data_reg[23:16]);
  cover property (cnt==2'b11 && vga_data == data_reg[23:16]);
  // cover gating low at cnt==0 and high when enabled
  cover property (cnt==2'b00 && !blank_out && !hs_out && !vs_out);
  cover property ((cnt!=2'b00) && blank_reg && hs_reg && vs_reg &&
                  blank_out && hs_out && vs_out);
  // cover data_reg update after sync boundary
  cover property (sync_pulse |=> (cnt==2'b11 && $past(data) == $past(data)) ##0 data_reg == $past(data));

endmodule

bind vga_converter vga_converter_sva sva_inst (
  .clk,
  .data,
  .blank,
  .hs,
  .vs,
  .vga_data,
  .blank_out,
  .hs_out,
  .vs_out,
  .cnt,
  .data_reg,
  .hs_reg,
  .hs_reg1,
  .vs_reg,
  .blank_reg
);