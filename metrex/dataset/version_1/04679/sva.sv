// SVA for dual_ps2_ioadapter
// Concise checks for connectivity, constants, and tri-state controls.

`ifndef DUAL_PS2_IOADAPTER_SVA
`define DUAL_PS2_IOADAPTER_SVA

// synthesis translate_off
module dual_ps2_ioadapter_sva
(
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

  // Invariants: continuous wiring, constants, and inversions
  always_comb begin
    // RX pass-throughs
    assert (ps2_clk_rx_1   === ps2_mouse_clk_I)
      else $error("ps2_clk_rx_1 must mirror ps2_mouse_clk_I");
    assert (ps2_clk_rx_2   === ps2_keyb_clk_I)
      else $error("ps2_clk_rx_2 must mirror ps2_keyb_clk_I");
    assert (ps2_d_rx_1     === ps2_mouse_data_I)
      else $error("ps2_d_rx_1 must mirror ps2_mouse_data_I");
    assert (ps2_d_rx_2     === ps2_keyb_data_I)
      else $error("ps2_d_rx_2 must mirror ps2_keyb_data_I");

    // Constant drive outputs
    assert (ps2_mouse_clk_O  === 1'b0) else $error("ps2_mouse_clk_O must be 0");
    assert (ps2_mouse_data_O === 1'b0) else $error("ps2_mouse_data_O must be 0");
    assert (ps2_keyb_clk_O   === 1'b0) else $error("ps2_keyb_clk_O must be 0");
    assert (ps2_keyb_data_O  === 1'b0) else $error("ps2_keyb_data_O must be 0");

    // Tri-state enables: must be exact inversions of TX intent
    assert (ps2_mouse_clk_T  === ~ps2_clk_tx_1) else $error("ps2_mouse_clk_T must be ~ps2_clk_tx_1");
    assert (ps2_mouse_data_T === ~ps2_d_tx_1)   else $error("ps2_mouse_data_T must be ~ps2_d_tx_1");
    assert (ps2_keyb_clk_T   === ~ps2_clk_tx_2) else $error("ps2_keyb_clk_T must be ~ps2_clk_tx_2");
    assert (ps2_keyb_data_T  === ~ps2_d_tx_2)   else $error("ps2_keyb_data_T must be ~ps2_d_tx_2");
  end

  // Edge-based checks for tri-state control behavior
  assert property (@(posedge ps2_clk_tx_1) ps2_mouse_clk_T  === 1'b0);
  assert property (@(negedge ps2_clk_tx_1) ps2_mouse_clk_T  === 1'b1);

  assert property (@(posedge ps2_d_tx_1)   ps2_mouse_data_T === 1'b0);
  assert property (@(negedge ps2_d_tx_1)   ps2_mouse_data_T === 1'b1);

  assert property (@(posedge ps2_clk_tx_2) ps2_keyb_clk_T   === 1'b0);
  assert property (@(negedge ps2_clk_tx_2) ps2_keyb_clk_T   === 1'b1);

  assert property (@(posedge ps2_d_tx_2)   ps2_keyb_data_T  === 1'b0);
  assert property (@(negedge ps2_d_tx_2)   ps2_keyb_data_T  === 1'b1);

  // Coverage: observe both 0/1 on RX paths
  cover property (@(posedge ps2_mouse_clk_I)  ps2_clk_rx_1   === 1'b1);
  cover property (@(negedge ps2_mouse_clk_I)  ps2_clk_rx_1   === 1'b0);
  cover property (@(posedge ps2_keyb_clk_I)   ps2_clk_rx_2   === 1'b1);
  cover property (@(negedge ps2_keyb_clk_I)   ps2_clk_rx_2   === 1'b0);

  cover property (@(posedge ps2_mouse_data_I) ps2_d_rx_1     === 1'b1);
  cover property (@(negedge ps2_mouse_data_I) ps2_d_rx_1     === 1'b0);
  cover property (@(posedge ps2_keyb_data_I)  ps2_d_rx_2     === 1'b1);
  cover property (@(negedge ps2_keyb_data_I)  ps2_d_rx_2     === 1'b0);

  // Coverage: both tri-state states observed for each channel
  cover property (@(posedge ps2_clk_tx_1)     ps2_mouse_clk_T  === 1'b0);
  cover property (@(negedge ps2_clk_tx_1)     ps2_mouse_clk_T  === 1'b1);
  cover property (@(posedge ps2_d_tx_1)       ps2_mouse_data_T === 1'b0);
  cover property (@(negedge ps2_d_tx_1)       ps2_mouse_data_T === 1'b1);

  cover property (@(posedge ps2_clk_tx_2)     ps2_keyb_clk_T   === 1'b0);
  cover property (@(negedge ps2_clk_tx_2)     ps2_keyb_clk_T   === 1'b1);
  cover property (@(posedge ps2_d_tx_2)       ps2_keyb_data_T  === 1'b0);
  cover property (@(negedge ps2_d_tx_2)       ps2_keyb_data_T  === 1'b1);

endmodule

bind dual_ps2_ioadapter dual_ps2_ioadapter_sva dut_sva (.*);
// synthesis translate_on

`endif