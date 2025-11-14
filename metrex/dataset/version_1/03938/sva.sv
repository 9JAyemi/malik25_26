// SVA checker for switch_bit. Bind this module to your DUT and drive clk from any TB clock.
// Example bind (connect clk and all DUT ports by name):
// bind switch_bit switch_bit_sva u_switch_bit_sva (.* , .clk(tb_clk));

module switch_bit_sva(
  input  logic                     clk,

  input  logic [3:0]               gpio_sel,
  input  logic [7:0]               tri_i_in,
  input  logic [7:0]               tri_o_in,
  input  logic [7:0]               tri_t_in,
  input  logic                     tri_i_out,
  input  logic                     tri_o_out,
  input  logic                     tri_t_out,
  input  logic                     pwm_i_in,
  input  logic                     pwm_o_in,
  input  logic                     pwm_t_in,
  input  logic                     cap0_i_in,
  input  logic                     gen0_o_in,
  input  logic                     gen0_t_in,
  input  logic                     spick_i_in,
  input  logic                     spick_o_in,
  input  logic                     spick_t_in,
  input  logic                     miso_i_in,
  input  logic                     miso_o_in,
  input  logic                     miso_t_in,
  input  logic                     mosi_i_in,
  input  logic                     mosi_o_in,
  input  logic                     mosi_t_in,
  input  logic                     ss_i_in,
  input  logic                     ss_o_in,
  input  logic                     ss_t_in,
  input  logic                     sda_i_in,
  input  logic                     sda_o_in,
  input  logic                     sda_t_in,
  input  logic                     scl_i_in,
  input  logic                     scl_o_in,
  input  logic                     scl_t_in
);

  default clocking cb @(posedge clk); endclocking

  // Expected mux outputs
  let o_sel_val =
      (gpio_sel<=4'h7) ? tri_o_in[gpio_sel] :
      (gpio_sel==4'h8) ? scl_o_in :
      (gpio_sel==4'h9) ? sda_o_in :
      (gpio_sel==4'hA) ? spick_o_in :
      (gpio_sel==4'hB) ? miso_o_in :
      (gpio_sel==4'hC) ? mosi_o_in :
      (gpio_sel==4'hD) ? ss_o_in   :
      (gpio_sel==4'hE) ? pwm_o_in  :
      (gpio_sel==4'hF) ? gen0_o_in : 1'b0;

  let t_sel_val =
      (gpio_sel<=4'h7) ? tri_t_in[gpio_sel] :
      (gpio_sel==4'h8) ? scl_t_in :
      (gpio_sel==4'h9) ? sda_t_in :
      (gpio_sel==4'hA) ? spick_t_in :
      (gpio_sel==4'hB) ? miso_t_in :
      (gpio_sel==4'hC) ? mosi_t_in :
      (gpio_sel==4'hD) ? ss_t_in   :
      (gpio_sel==4'hE) ? pwm_t_in  :
      (gpio_sel==4'hF) ? gen0_t_in : 1'b0;

  // Reconstruct the internal 16b demux bus at the outputs
  let demux_bus      = {cap0_i_in,pwm_i_in,ss_i_in,mosi_i_in,miso_i_in,spick_i_in,sda_i_in,scl_i_in,tri_i_in};
  let exp_demux_bus  = tri_i_out ? (16'h0001 << gpio_sel) : 16'h0000;

  // Core checks
  a_o_mux: assert property (disable iff ($isunknown({gpio_sel,tri_o_in,scl_o_in,sda_o_in,spick_o_in,miso_o_in,mosi_o_in,ss_o_in,pwm_o_in,gen0_o_in}))
                            tri_o_out === o_sel_val);

  a_t_mux: assert property (disable iff ($isunknown({gpio_sel,tri_t_in,scl_t_in,sda_t_in,spick_t_in,miso_t_in,mosi_t_in,ss_t_in,pwm_t_in,gen0_t_in}))
                            tri_t_out === t_sel_val);

  a_demux: assert property (disable iff ($isunknown({gpio_sel,tri_i_out}))
                            demux_bus === exp_demux_bus);

  a_onehot0_demux: assert property (disable iff ($isunknown({demux_bus})) $onehot0(demux_bus));

  // Basic functional coverage
  genvar i;
  generate
    for (i=0; i<16; i++) begin : g_cov_sel
      c_sel: cover property (gpio_sel == i[3:0]);
    end
  endgenerate

  c_demux_on:  cover property (tri_i_out && (demux_bus == (16'h0001 << gpio_sel)));
  c_demux_off: cover property (!tri_i_out && (demux_bus == 16'h0000));

  c_o_mux_any: cover property ($changed(gpio_sel) ##0 (tri_o_out === o_sel_val));
  c_t_mux_any: cover property ($changed(gpio_sel) ##0 (tri_t_out === t_sel_val));

endmodule