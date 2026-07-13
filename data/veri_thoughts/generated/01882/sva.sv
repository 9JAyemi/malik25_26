module dual_ps2_ioadapter_sva (
  input logic ps2_clk_rx_1,
  input logic ps2_clk_rx_2,
  input logic ps2_clk_tx_1,
  input logic ps2_clk_tx_2,
  input logic ps2_d_rx_1,
  input logic ps2_d_rx_2,
  input logic ps2_d_tx_1,
  input logic ps2_d_tx_2,
  input logic ps2_mouse_clk_I,
  input logic ps2_mouse_clk_O,
  input logic ps2_mouse_clk_T,
  input logic ps2_mouse_data_I,
  input logic ps2_mouse_data_O,
  input logic ps2_mouse_data_T,
  input logic ps2_keyb_clk_I,
  input logic ps2_keyb_clk_O,
  input logic ps2_keyb_clk_T,
  input logic ps2_keyb_data_I,
  input logic ps2_keyb_data_O,
  input logic ps2_keyb_data_T
);
  ///// Mouse channel wiring /////
  // ps2_clk_rx_1 mirrors ps2_mouse_clk_I.
  check_mouse_clk_rx_maps_mouse_clk_I: assert property (
    @(posedge ps2_mouse_clk_I) ps2_clk_rx_1 === ps2_mouse_clk_I
  );
  // ps2_d_rx_1 mirrors ps2_mouse_data_I.
  check_mouse_data_rx_maps_mouse_data_I: assert property (
    @(posedge ps2_mouse_clk_I) ps2_d_rx_1 === ps2_mouse_data_I
  );
  // ps2_mouse_clk_O is tied LOW.
  check_mouse_clk_o_is_zero: assert property (
    @(posedge ps2_mouse_clk_I) ps2_mouse_clk_O === 1'b0
  );
  // ps2_mouse_data_O is tied LOW.
  check_mouse_data_o_is_zero: assert property (
    @(posedge ps2_mouse_clk_I) ps2_mouse_data_O === 1'b0
  );
  // ps2_mouse_clk_T is inverse of ps2_clk_tx_1.
  check_mouse_clk_t_is_inv_tx1: assert property (
    @(posedge ps2_mouse_clk_I) ps2_mouse_clk_T === ~ps2_clk_tx_1
  );
  // ps2_mouse_data_T is inverse of ps2_d_tx_1.
  check_mouse_data_t_is_inv_tx1: assert property (
    @(posedge ps2_mouse_clk_I) ps2_mouse_data_T === ~ps2_d_tx_1
  );

  ///// Keyboard channel wiring /////
  // ps2_clk_rx_2 mirrors ps2_keyb_clk_I.
  check_keyb_clk_rx_maps_keyb_clk_I: assert property (
    @(posedge ps2_keyb_clk_I) ps2_clk_rx_2 === ps2_keyb_clk_I
  );
  // ps2_d_rx_2 mirrors ps2_keyb_data_I.
  check_keyb_data_rx_maps_keyb_data_I: assert property (
    @(posedge ps2_keyb_clk_I) ps2_d_rx_2 === ps2_keyb_data_I
  );
  // ps2_keyb_clk_O is tied LOW.
  check_keyb_clk_o_is_zero: assert property (
    @(posedge ps2_keyb_clk_I) ps2_keyb_clk_O === 1'b0
  );
  // ps2_keyb_data_O is tied LOW.
  check_keyb_data_o_is_zero: assert property (
    @(posedge ps2_keyb_clk_I) ps2_keyb_data_O === 1'b0
  );
  // ps2_keyb_clk_T is inverse of ps2_clk_tx_2.
  check_keyb_clk_t_is_inv_tx2: assert property (
    @(posedge ps2_keyb_clk_I) ps2_keyb_clk_T === ~ps2_clk_tx_2
  );
  // ps2_keyb_data_T is inverse of ps2_d_tx_2.
  check_keyb_data_t_is_inv_tx2: assert property (
    @(posedge ps2_keyb_clk_I) ps2_keyb_data_T === ~ps2_d_tx_2
  );
endmodule