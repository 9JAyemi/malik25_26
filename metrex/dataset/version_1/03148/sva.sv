// SVA for hpdmc_busif
// Bind-friendly, concise, and covers key behavior

module hpdmc_busif_sva #(
  parameter int sdram_depth = 23
)(
  input  logic                         sys_clk,
  input  logic                         sdram_rst,

  input  logic [sdram_depth-1:0]       fml_adr,
  input  logic                         fml_stb,
  input  logic                         fml_we,
  output logic                         fml_ack,     // for bind .*

  output logic                         mgmt_stb,    // for bind .*
  output logic                         mgmt_we,     // for bind .*
  output logic [sdram_depth-2:0]       mgmt_address,// for bind .*
  input  logic                         mgmt_ack,

  input  logic                         data_ack,

  // internal signal (hierarchical bind)
  input  logic                         mgmt_stb_en
);

  default clocking cb @(posedge sys_clk); endclocking

  // Combinational relations
  ap_mgmt_stb_eq:    assert property (disable iff (sdram_rst) mgmt_stb == (fml_stb & mgmt_stb_en));
  ap_mgmt_we_eq:     assert property (mgmt_we == fml_we);
  ap_addr_eq:        assert property (mgmt_address == fml_adr[sdram_depth-1:1]);
  ap_ack_passthru:   assert property (fml_ack == data_ack);

  // Reset behavior (synchronous)
  ap_rst_sets_en:    assert property (sdram_rst |=> mgmt_stb_en);

  // Next-state function for mgmt_stb_en (blocking assignment priority: data_ack wins over mgmt_ack)
  ap_en_next_data:   assert property (disable iff (sdram_rst) data_ack |=> mgmt_stb_en);
  ap_en_next_ack:    assert property (disable iff (sdram_rst) mgmt_ack && !data_ack |=> !mgmt_stb_en);
  ap_en_next_hold:   assert property (disable iff (sdram_rst) !mgmt_ack && !data_ack |=> mgmt_stb_en == $past(mgmt_stb_en));
  ap_en_next_both:   assert property (disable iff (sdram_rst) mgmt_ack && data_ack |=> mgmt_stb_en);

  // Known-value checks (avoid X/Z on outputs when out of reset)
  ap_known_outs:     assert property (disable iff (sdram_rst) !$isunknown({mgmt_stb, mgmt_we, mgmt_address, fml_ack}));
  ap_known_en:       assert property (disable iff (sdram_rst) !$isunknown(mgmt_stb_en));

  // Coverage
  cv_reset_sets_en:  cover property (sdram_rst ##1 mgmt_stb_en);
  cv_en_drop_on_ack: cover property (mgmt_stb_en ##1 mgmt_ack && !data_ack ##1 !mgmt_stb_en);
  cv_en_set_on_data: cover property (!mgmt_stb_en ##1 data_ack ##1 mgmt_stb_en);
  cv_both_acks:      cover property (mgmt_ack && data_ack ##1 mgmt_stb_en);
  cv_mgmt_stb:       cover property (fml_stb && mgmt_stb_en && mgmt_stb);

endmodule

// Bind example:
// bind hpdmc_busif hpdmc_busif_sva #(.sdram_depth(sdram_depth)) u_hpdmc_busif_sva (.* , .mgmt_stb_en(mgmt_stb_en));