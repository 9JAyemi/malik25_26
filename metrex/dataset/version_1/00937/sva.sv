// SVA for axi_ad9680_if
// Bind into DUT scope so we can check internal nets and outputs

bind axi_ad9680_if axi_ad9680_if_sva sva();

module axi_ad9680_if_sva;

  // Local expected decode from rx_data
  logic [55:0] exp_a, exp_b;
  always_comb begin
    exp_a = { rx_data[31:24], rx_data[63:58],
              rx_data[23:16], rx_data[55:50],
              rx_data[15: 8], rx_data[47:42],
              rx_data[ 7: 0], rx_data[39:34] };

    exp_b = { rx_data[95:88],  rx_data[127:122],
              rx_data[87:80],  rx_data[119:114],
              rx_data[79:72],  rx_data[111:106],
              rx_data[71:64],  rx_data[103: 98] };
  end

  default clocking cb @(posedge rx_clk); endclocking

  // Clock passthrough checks (both edges)
  assert property (@(posedge rx_clk) $rose(adc_clk));
  assert property (@(negedge rx_clk) $fell(adc_clk));

  // OR flags are tied low
  assert property (cb adc_or_a == 1'b0);
  assert property (cb adc_or_b == 1'b0);

  // adc_status behavior: synchronous 0 during reset, 1 otherwise (on next cycle)
  assert property (cb adc_rst |=> adc_status == 1'b0);
  assert property (cb !adc_rst |=> adc_status == 1'b1);

  // No X/Z on outputs when inputs are known
  assert property (cb !$isunknown(rx_data) |-> !$isunknown({adc_data_a, adc_data_b}));
  assert property (cb !$isunknown(rx_clk)  |-> !$isunknown(adc_clk));
  assert property (cb !$isunknown(adc_rst) |-> !$isunknown(adc_status));

  // Internal slice wiring correctness (A)
  assert property (cb adc_data_a_s3_s == {rx_data[ 57: 56], rx_data[31:24], rx_data[ 63:58]});
  assert property (cb adc_data_a_s2_s == {rx_data[ 49: 48], rx_data[23:16], rx_data[ 55:50]});
  assert property (cb adc_data_a_s1_s == {rx_data[ 41: 40], rx_data[15: 8], rx_data[ 47:42]});
  assert property (cb adc_data_a_s0_s == {rx_data[ 33: 32], rx_data[ 7: 0], rx_data[ 39:34]});

  // Internal slice wiring correctness (B)
  assert property (cb adc_data_b_s3_s == {rx_data[121:120], rx_data[95:88], rx_data[127:122]});
  assert property (cb adc_data_b_s2_s == {rx_data[113:112], rx_data[87:80], rx_data[119:114]});
  assert property (cb adc_data_b_s1_s == {rx_data[105:104], rx_data[79:72], rx_data[111:106]});
  assert property (cb adc_data_b_s0_s == {rx_data[ 97: 96], rx_data[71:64], rx_data[103: 98]});

  // Output concatenation matches expected decode directly from rx_data
  assert property (cb adc_data_a == exp_a);
  assert property (cb adc_data_b == exp_b);

  // Optional: outputs match concatenation of internal slices' [13:0]
  assert property (cb adc_data_a ==
                      { adc_data_a_s3_s[13:0], adc_data_a_s2_s[13:0],
                        adc_data_a_s1_s[13:0], adc_data_a_s0_s[13:0]});
  assert property (cb adc_data_b ==
                      { adc_data_b_s3_s[13:0], adc_data_b_s2_s[13:0],
                        adc_data_b_s1_s[13:0], adc_data_b_s0_s[13:0]});

  // Coverage
  cover property (cb $rose(adc_rst));             // reset asserted
  cover property (cb $fell(adc_rst));             // reset deasserted
  cover property (cb !adc_rst && adc_status);     // in-active reset, status high
  cover property (cb !$isunknown(rx_data) && $changed(adc_data_a));
  cover property (cb !$isunknown(rx_data) && $changed(adc_data_b));
  cover property (@(posedge rx_clk) $rose(adc_clk));
  cover property (@(negedge rx_clk) $fell(adc_clk));

endmodule