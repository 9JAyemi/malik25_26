// SVA for wireless_communication_block
// Bind these into the DUT; concise, high-quality functional checks and coverage

module wc_sva (
  input  logic [7:0] data_in,
  input  logic [1:0] ctrl,
  input  logic [7:0] data_out,
  input  logic [7:0] bt,
  input  logic [7:0] wifi,
  input  logic [7:0] zigbee
);

  // Core mux correctness
  a_mux_sel: assert property (@(*)
    data_out == ((ctrl==2'b00) ? bt :
                 (ctrl==2'b01) ? wifi :
                 (ctrl==2'b10) ? zigbee : 8'h00));

  // Submodules must be transparent
  a_bt_passthru:   assert property (@(*)) bt   == data_in;
  a_wifi_passthru: assert property (@(*)) wifi == data_in;
  a_zb_passthru:   assert property (@(*)) zigbee == data_in;

  // Selected path yields data_in; reserved code yields zero
  a_sel_eq_in: assert property (@(*)) (ctrl inside {2'b00,2'b01,2'b10}) |-> (data_out == data_in);
  a_res_zero:  assert property (@(*)) (ctrl == 2'b11) |-> (data_out == 8'h00);

  // No X/Z on output if inputs are known
  a_no_x: assert property (@(*)) !$isunknown({ctrl, data_in}) |-> !$isunknown(data_out);

  // Combinational stability: if inputs stable, output stable
  a_stable: assert property (@(*)) $stable({ctrl, data_in}) |-> $stable(data_out);

  // Functional coverage: all selections and reserved behavior observed
  c_sel00: cover property (@(*)) (ctrl==2'b00) && (data_out==data_in);
  c_sel01: cover property (@(*)) (ctrl==2'b01) && (data_out==data_in);
  c_sel10: cover property (@(*)) (ctrl==2'b10) && (data_out==data_in);
  c_sel11: cover property (@(*)) (ctrl==2'b11) && (data_out==8'h00);

  // Cover cycling through all modes
  c_cycle_modes: cover property (@(*)) (ctrl==2'b00) ##1 (ctrl==2'b01) ##1 (ctrl==2'b10) ##1 (ctrl==2'b11);

endmodule

// Bind into DUT (connect to internal nets for deep checking)
bind wireless_communication_block wc_sva i_wc_sva (
  .data_in(data_in),
  .ctrl(ctrl),
  .data_out(data_out),
  .bt(bt_module_data_out),
  .wifi(wifi_module_data_out),
  .zigbee(zigbee_module_data_out)
);