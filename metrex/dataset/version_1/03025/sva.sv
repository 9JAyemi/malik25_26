// SVA for reset_and_status
// Concise checks + functional coverage
`ifndef SYNTHESIS
module reset_and_status_sva
  #(parameter int PIO_WIDTH=32)
(
  input  logic                     clk,
  input  logic                     resetn,

  input  logic [PIO_WIDTH-1:0]     pio_in,
  input  logic [PIO_WIDTH-1:0]     pio_out,

  input  logic                     lock_kernel_pll,
  input  logic                     fixedclk_locked,
  input  logic                     mem0_local_cal_success,
  input  logic                     mem0_local_cal_fail,
  input  logic                     mem0_local_init_done,
  input  logic                     mem1_local_cal_success,
  input  logic                     mem1_local_cal_fail,
  input  logic                     mem1_local_init_done,

  input  logic [1:0]               mem_organization,
  input  logic [1:0]               mem_organization_export,
  input  logic                     pll_reset,
  input  logic                     sw_reset_n_out,

  // internal taps
  input  logic [1:0]               pio_out_ddr_mode,
  input  logic                     pio_out_pll_reset,
  input  logic                     pio_out_sw_reset,
  input  logic [9:0]               reset_count
);

  // Basic no-X on key outputs when out of reset
  assert property (@(posedge clk) resetn |-> !$isunknown({pll_reset, sw_reset_n_out, mem_organization, mem_organization_export}));

  // Mappings from pio_out sampling
  assert property (@(posedge clk) pll_reset == pio_out[30]);
  assert property (@(posedge clk) mem_organization == pio_out[9:8]);
  assert property (@(posedge clk) mem_organization_export == mem_organization);

  // Internal sample correctness
  assert property (@(posedge clk) pio_out_ddr_mode  == pio_out[9:8]);
  assert property (@(posedge clk) pio_out_pll_reset == pio_out[30]);
  assert property (@(posedge clk) pio_out_sw_reset  == pio_out[31]);

  // pio_in mapping (low 10 bits) and zero-extension on upper bits
  assert property (@(posedge clk)
    pio_in[9:0] == { lock_kernel_pll,
                     fixedclk_locked,
                     1'b0,
                     1'b0,
                     mem1_local_cal_fail,
                     mem0_local_cal_fail,
                     mem1_local_cal_success,
                     mem1_local_init_done,
                     mem0_local_cal_success,
                     mem0_local_init_done });
  if (PIO_WIDTH > 10) begin
    assert property (@(posedge clk) pio_in[PIO_WIDTH-1:10] == '0);
  end

  // reset_count behavior
  // Asynchronous reset holds counter at 0 whenever resetn==0
  assert property (@(posedge clk) !resetn |-> reset_count == 10'd0);
  // Software reset forces counter to 0 in the same cycle
  assert property (@(posedge clk) pio_out_sw_reset |-> reset_count == 10'd0);
  // Increment while MSB not set and no sw reset
  assert property (@(posedge clk) disable iff (!resetn)
                   (!pio_out_sw_reset && !reset_count[9]) |=> reset_count == $past(reset_count) + 10'd1);
  // Hold once MSB set (unless sw reset asserted)
  assert property (@(posedge clk) disable iff (!resetn)
                   ($past(reset_count[9]) && !pio_out_sw_reset) |-> reset_count == $past(reset_count));

  // sw_reset_n_out exact function of reset_count
  assert property (@(posedge clk)
    sw_reset_n_out == (reset_count[9] || (reset_count[8:0] == 9'd0)));

  // Functional coverage
  // Counter progresses to MSB set after coming out of reset
  cover property (@(posedge clk) $rose(resetn) ##[1:$] reset_count[9]);
  // Counter progression after a software reset pulse
  cover property (@(posedge clk) pio_out_sw_reset ##1 !pio_out_sw_reset ##[1:$] reset_count[9]);
  // sw_reset_n_out 1->0->1 pattern across the count window
  cover property (@(posedge clk) sw_reset_n_out ##1 !sw_reset_n_out ##[1:$] sw_reset_n_out);
  // Observe mem_organization change driven by pio_out
  cover property (@(posedge clk) $changed(mem_organization));

endmodule

bind reset_and_status reset_and_status_sva #(.PIO_WIDTH(PIO_WIDTH)) i_reset_and_status_sva (.*);
`endif