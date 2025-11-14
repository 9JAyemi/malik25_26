// SVA for arduino_switch_digital_uart_bit
// Bind this module to the DUT for checks and coverage.
module arduino_switch_digital_uart_bit_sva(
  input  logic gpio_sel,
  input  logic tri_i_out,
  input  logic tri_o_in,
  input  logic tx_o_in,
  input  logic tri_t_in,
  input  logic tx_t_in,
  input  logic tri_o_out,
  input  logic tri_t_out,
  input  logic tri_i_in,
  input  logic rx_i_in
);

  // Mux correctness: data out
  property p_tri_o_mux;
    @(gpio_sel or tri_o_in or tx_o_in)
      (!$isunknown({gpio_sel,tri_o_in,tx_o_in}))
      |-> (tri_o_out == (gpio_sel ? tx_o_in : tri_o_in));
  endproperty
  assert property (p_tri_o_mux);

  // Mux correctness: tri-state control out
  property p_tri_t_mux;
    @(gpio_sel or tri_t_in or tx_t_in)
      (!$isunknown({gpio_sel,tri_t_in,tx_t_in}))
      |-> (tri_t_out == (gpio_sel ? tx_t_in : tri_t_in));
  endproperty
  assert property (p_tri_t_mux);

  // Demux correctness: mapping and gating
  property p_demux_map;
    @(gpio_sel or tri_i_out)
      (!$isunknown({gpio_sel,tri_i_out}))
      |-> ( tri_i_in == (gpio_sel ? 1'b0     : tri_i_out)
         && rx_i_in == (gpio_sel ? tri_i_out : 1'b0) );
  endproperty
  assert property (p_demux_map);

  // Demux consistency: exclusivity and conservation
  property p_demux_consistency;
    @(tri_i_in or rx_i_in or tri_i_out)
      (!$isunknown({tri_i_in,rx_i_in,tri_i_out}))
      |-> ( (tri_i_in & rx_i_in) == 1'b0
         && (tri_i_in | rx_i_in) == tri_i_out );
  endproperty
  assert property (p_demux_consistency);

  // Non-interference: unselected path does not affect outputs
  property p_unselected_tx_data_no_effect;
    @(tx_o_in) (!gpio_sel && !$isunknown({gpio_sel,tri_o_in,tx_o_in}))
      |-> (tri_o_out == tri_o_in);
  endproperty
  assert property (p_unselected_tx_data_no_effect);

  property p_unselected_tri_data_no_effect;
    @(tri_o_in) (gpio_sel && !$isunknown({gpio_sel,tri_o_in,tx_o_in}))
      |-> (tri_o_out == tx_o_in);
  endproperty
  assert property (p_unselected_tri_data_no_effect);

  property p_unselected_tx_t_no_effect;
    @(tx_t_in) (!gpio_sel && !$isunknown({gpio_sel,tri_t_in,tx_t_in}))
      |-> (tri_t_out == tri_t_in);
  endproperty
  assert property (p_unselected_tx_t_no_effect);

  property p_unselected_tri_t_no_effect;
    @(tri_t_in) (gpio_sel && !$isunknown({gpio_sel,tri_t_in,tx_t_in}))
      |-> (tri_t_out == tx_t_in);
  endproperty
  assert property (p_unselected_tri_t_no_effect);

  // Demux unselected leg forced low
  property p_demux_unselected_forced_low_lo;
    @(tri_i_out) (!gpio_sel && !$isunknown({gpio_sel,tri_i_out}))
      |-> (rx_i_in == 1'b0 && tri_i_in == tri_i_out);
  endproperty
  assert property (p_demux_unselected_forced_low_lo);

  property p_demux_unselected_forced_low_hi;
    @(tri_i_out) (gpio_sel && !$isunknown({gpio_sel,tri_i_out}))
      |-> (tri_i_in == 1'b0 && rx_i_in == tri_i_out);
  endproperty
  assert property (p_demux_unselected_forced_low_hi);

  // X-prop on outputs when driving inputs/select are known
  assert property (@(gpio_sel or tri_o_in or tx_o_in)
                   (!$isunknown({gpio_sel,tri_o_in,tx_o_in})) |-> !$isunknown(tri_o_out));
  assert property (@(gpio_sel or tri_t_in or tx_t_in)
                   (!$isunknown({gpio_sel,tri_t_in,tx_t_in})) |-> !$isunknown(tri_t_out));
  assert property (@(gpio_sel or tri_i_out)
                   (!$isunknown({gpio_sel,tri_i_out})) |-> !$isunknown({tri_i_in,rx_i_in}));

  // Coverage: exercise both select paths and data flow
  cover property (@(gpio_sel) (gpio_sel==1'b0));
  cover property (@(gpio_sel) (gpio_sel==1'b1));

  cover property (@(gpio_sel or tri_i_out or tri_o_in or tri_t_in)
                  (!gpio_sel && tri_i_out && (tri_i_in==1) && (rx_i_in==0)
                   && (tri_o_out==tri_o_in) && (tri_t_out==tri_t_in)));

  cover property (@(gpio_sel or tri_i_out or tx_o_in or tx_t_in)
                  (gpio_sel && tri_i_out && (rx_i_in==1) && (tri_i_in==0)
                   && (tri_o_out==tx_o_in) && (tri_t_out==tx_t_in)));

endmodule

bind arduino_switch_digital_uart_bit arduino_switch_digital_uart_bit_sva
(
  .gpio_sel(gpio_sel),
  .tri_i_out(tri_i_out),
  .tri_o_in(tri_o_in),
  .tx_o_in(tx_o_in),
  .tri_t_in(tri_t_in),
  .tx_t_in(tx_t_in),
  .tri_o_out(tri_o_out),
  .tri_t_out(tri_t_out),
  .tri_i_in(tri_i_in),
  .rx_i_in(rx_i_in)
);