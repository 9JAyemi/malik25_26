// SVA for NIOS_SYSTEMV3_NIOS_CPU_nios2_avalon_reg
// Concise checks + coverage of address decode, read mux, reset, and write side-effects

module nios2_avalon_reg_sva
(
  input         clk,
  input         reset_n,

  input  [8:0]  address,
  input         debugaccess,
  input         write,
  input  [31:0] writedata,

  input         monitor_error,
  input         monitor_ready,
  input         monitor_go,

  input  [31:0] oci_ienable,
  input  [31:0] oci_reg_readdata,
  input         oci_single_step_mode,
  input         ocireg_ers,
  input         ocireg_mrs,
  input         take_action_ocireg
);
  localparam [8:0] ADDR0 = 9'h100;
  localparam [8:0] ADDR1 = 9'h101;

  wire addr0 = (address == ADDR0);
  wire addr1 = (address == ADDR1);
  wire ws    = write & debugaccess;

  // Basic decode consistency
  assert property (@(posedge clk) !(addr0 && addr1));

  // Reset values must hold while reset asserted
  assert property (@(posedge clk) !reset_n |-> (oci_single_step_mode == 1'b0 && oci_ienable == 32'h0000_0001));

  // Take-action decode
  assert property (@(posedge clk) take_action_ocireg == (ws & addr0));

  // Combinational field mapping from writedata
  assert property (@(posedge clk) ocireg_ers == writedata[1]);
  assert property (@(posedge clk) ocireg_mrs == writedata[0]);

  // Read mux correctness
  assert property (@(posedge clk) addr0 |-> (oci_reg_readdata == {28'b0, oci_single_step_mode, monitor_go, monitor_ready, monitor_error}));
  assert property (@(posedge clk) addr1 |-> (oci_reg_readdata == oci_ienable));
  assert property (@(posedge clk) (!addr0 && !addr1) |-> (oci_reg_readdata == 32'b0));

  // oci_single_step_mode update/hold
  assert property (@(posedge clk) disable iff (!reset_n)
                   (ws && addr0) |=> (oci_single_step_mode == $past(writedata[3])));
  assert property (@(posedge clk) disable iff (!reset_n)
                   !(ws && addr0) |=> $stable(oci_single_step_mode));

  // oci_ienable update/hold (bit0 from writedata[0], others forced to 1 on write to ADDR1)
  assert property (@(posedge clk) disable iff (!reset_n)
                   (ws && addr1) |=> (oci_ienable == ($past(writedata) | 32'hFFFF_FFFE)));
  assert property (@(posedge clk) disable iff (!reset_n)
                   !(ws && addr1) |=> $stable(oci_ienable));

  // No side-effects when writing other addresses
  assert property (@(posedge clk) disable iff (!reset_n)
                   (ws && !addr0 && !addr1) |=> ($stable(oci_single_step_mode) && $stable(oci_ienable)));

  // Coverage
  cover property (@(posedge clk) !reset_n ##1 reset_n); // reset release
  cover property (@(posedge clk) disable iff (!reset_n) ws && addr0); // write to reg0
  cover property (@(posedge clk) disable iff (!reset_n) ws && addr1); // write to reg1
  cover property (@(posedge clk) disable iff (!reset_n)
                  (ws && addr0 &&  writedata[3]) ##1 (oci_single_step_mode == 1'b1)
                  ##1 (ws && addr0 && !writedata[3]) ##1 (oci_single_step_mode == 1'b0));
  cover property (@(posedge clk) disable iff (!reset_n)
                  (ws && addr1 && !writedata[0]) ##1 (oci_ienable == 32'hFFFF_FFFE)
                  ##1 (ws && addr1 &&  writedata[0]) ##1 (oci_ienable == 32'hFFFF_FFFF));
  cover property (@(posedge clk) disable iff (!reset_n) (!addr0 && !addr1) && (oci_reg_readdata == 32'h0));

endmodule

bind NIOS_SYSTEMV3_NIOS_CPU_nios2_avalon_reg
  nios2_avalon_reg_sva sva_i
  (
    .clk                (clk),
    .reset_n            (reset_n),
    .address            (address),
    .debugaccess        (debugaccess),
    .write              (write),
    .writedata          (writedata),
    .monitor_error      (monitor_error),
    .monitor_ready      (monitor_ready),
    .monitor_go         (monitor_go),
    .oci_ienable        (oci_ienable),
    .oci_reg_readdata   (oci_reg_readdata),
    .oci_single_step_mode(oci_single_step_mode),
    .ocireg_ers         (ocireg_ers),
    .ocireg_mrs         (ocireg_mrs),
    .take_action_ocireg (take_action_ocireg)
  );