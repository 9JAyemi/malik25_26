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

  ///// RX mappings /////
  // Mouse clock RX mirrors mouse clock input (posedge).
  mirror_mouse_clk_rx_pos: assert property (
    @(posedge ps2_mouse_clk_I) ##0 (ps2_clk_rx_1 == ps2_mouse_clk_I)
  );
  // Mouse clock RX mirrors mouse clock input (negedge).
  mirror_mouse_clk_rx_neg: assert property (
    @(negedge ps2_mouse_clk_I) ##0 (ps2_clk_rx_1 == ps2_mouse_clk_I)
  );
  // Keyboard clock RX mirrors keyboard clock input (posedge).
  mirror_keyb_clk_rx_pos: assert property (
    @(posedge ps2_keyb_clk_I) ##0 (ps2_clk_rx_2 == ps2_keyb_clk_I)
  );
  // Keyboard clock RX mirrors keyboard clock input (negedge).
  mirror_keyb_clk_rx_neg: assert property (
    @(negedge ps2_keyb_clk_I) ##0 (ps2_clk_rx_2 == ps2_keyb_clk_I)
  );
  // Mouse data RX mirrors mouse data input (posedge).
  mirror_mouse_data_rx_pos: assert property (
    @(posedge ps2_mouse_data_I) ##0 (ps2_d_rx_1 == ps2_mouse_data_I)
  );
  // Mouse data RX mirrors mouse data input (negedge).
  mirror_mouse_data_rx_neg: assert property (
    @(negedge ps2_mouse_data_I) ##0 (ps2_d_rx_1 == ps2_mouse_data_I)
  );
  // Keyboard data RX mirrors keyboard data input (posedge).
  mirror_keyb_data_rx_pos: assert property (
    @(posedge ps2_keyb_data_I) ##0 (ps2_d_rx_2 == ps2_keyb_data_I)
  );
  // Keyboard data RX mirrors keyboard data input (negedge).
  mirror_keyb_data_rx_neg: assert property (
    @(negedge ps2_keyb_data_I) ##0 (ps2_d_rx_2 == ps2_keyb_data_I)
  );

  ///// Tri-state control mappings /////
  // Mouse clock T is inverse of tx_1 (posedge).
  inv_mouse_clk_T_pos: assert property (
    @(posedge ps2_clk_tx_1) ##0 (ps2_mouse_clk_T == ~ps2_clk_tx_1)
  );
  // Mouse clock T is inverse of tx_1 (negedge).
  inv_mouse_clk_T_neg: assert property (
    @(negedge ps2_clk_tx_1) ##0 (ps2_mouse_clk_T == ~ps2_clk_tx_1)
  );
  // Mouse data T is inverse of d_tx_1 (posedge).
  inv_mouse_data_T_pos: assert property (
    @(posedge ps2_d_tx_1) ##0 (ps2_mouse_data_T == ~ps2_d_tx_1)
  );
  // Mouse data T is inverse of d_tx_1 (negedge).
  inv_mouse_data_T_neg: assert property (
    @(negedge ps2_d_tx_1) ##0 (ps2_mouse_data_T == ~ps2_d_tx_1)
  );
  // Keyboard clock T is inverse of tx_2 (posedge).
  inv_keyb_clk_T_pos: assert property (
    @(posedge ps2_clk_tx_2) ##0 (ps2_keyb_clk_T == ~ps2_clk_tx_2)
  );
  // Keyboard clock T is inverse of tx_2 (negedge).
  inv_keyb_clk_T_neg: assert property (
    @(negedge ps2_clk_tx_2) ##0 (ps2_keyb_clk_T == ~ps2_clk_tx_2)
  );
  // Keyboard data T is inverse of d_tx_2 (posedge).
  inv_keyb_data_T_pos: assert property (
    @(posedge ps2_d_tx_2) ##0 (ps2_keyb_data_T == ~ps2_d_tx_2)
  );
  // Keyboard data T is inverse of d_tx_2 (negedge).
  inv_keyb_data_T_neg: assert property (
    @(negedge ps2_d_tx_2) ##0 (ps2_keyb_data_T == ~ps2_d_tx_2)
  );

  ///// Constant drive on O pins /////
  // Mouse clock O is constant 0.
  const_mouse_clk_O: assert property (
    @(posedge ps2_clk_tx_1) ##0 (ps2_mouse_clk_O == 1'b0)
  );
  // Mouse data O is constant 0.
  const_mouse_data_O: assert property (
    @(posedge ps2_d_tx_1) ##0 (ps2_mouse_data_O == 1'b0)
  );
  // Keyboard clock O is constant 0.
  const_keyb_clk_O: assert property (
    @(posedge ps2_clk_tx_2) ##0 (ps2_keyb_clk_O == 1'b0)
  );
  // Keyboard data O is constant 0.
  const_keyb_data_O: assert property (
    @(posedge ps2_d_tx_2) ##0 (ps2_keyb_data_O == 1'b0)
  );

endmodule