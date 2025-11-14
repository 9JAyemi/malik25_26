// SVA for Altera_UP_I2C_DC_Auto_Initialize
// Bind this module to the DUT: 
//   bind Altera_UP_I2C_DC_Auto_Initialize Altera_UP_I2C_DC_Auto_Initialize_SVA sva();

module Altera_UP_I2C_DC_Auto_Initialize_SVA;

  // STATE encodings (mirror DUT)
  localparam AUTO_STATE_0_CHECK_STATUS   = 4'h0;
  localparam AUTO_STATE_1_SEND_START_BIT = 4'h1;
  localparam AUTO_STATE_2_TRANSFER_BYTE_0= 4'h2;
  localparam AUTO_STATE_3_TRANSFER_BYTE_1= 4'h3;
  localparam AUTO_STATE_4_TRANSFER_BYTE_2= 4'h4;
  localparam AUTO_STATE_5_WAIT           = 4'h5;
  localparam AUTO_STATE_6_SEND_STOP_BIT  = 4'h6;
  localparam AUTO_STATE_7_INCREASE_COUNTER=4'h7;
  localparam AUTO_STATE_8_DONE           = 4'h8;

  localparam MIN_ROM_ADDRESS = 5'h00;
  localparam MAX_ROM_ADDRESS = 5'h18;

  // Clocking and reset
  default clocking cb @(posedge clk); endclocking

  // Basic equivalences
  assert property (disable iff (reset) change_state == (transfer_complete & transfer_data));
  assert property (disable iff (reset) finished_auto_init == (rom_address_counter == MAX_ROM_ADDRESS));
  assert property (disable iff (reset) auto_init_complete == (s_i2c_auto_init == AUTO_STATE_8_DONE));
  // State register follows ns (sanity)
  assert property (disable iff (reset) s_i2c_auto_init == $past(ns_i2c_auto_init));

  // FSM transition correctness
  // 0: CHECK_STATUS
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS && finished_auto_init |=> s_i2c_auto_init == AUTO_STATE_8_DONE);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && rom_data[25] |=> s_i2c_auto_init == AUTO_STATE_1_SEND_START_BIT);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && !rom_data[25] |=> s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1);

  // 1..4: byte transfers
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_1_SEND_START_BIT && change_state |=> s_i2c_auto_init == AUTO_STATE_2_TRANSFER_BYTE_0);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_1_SEND_START_BIT && !change_state |=> s_i2c_auto_init == AUTO_STATE_1_SEND_START_BIT);

  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_2_TRANSFER_BYTE_0 && change_state |=> s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_2_TRANSFER_BYTE_0 && !change_state |=> s_i2c_auto_init == AUTO_STATE_2_TRANSFER_BYTE_0);

  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1 && change_state |=> s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1 && !change_state |=> s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1);

  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2 && change_state && rom_data[24] |=> s_i2c_auto_init == AUTO_STATE_5_WAIT);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2 && change_state && !rom_data[24] |=> s_i2c_auto_init == AUTO_STATE_7_INCREASE_COUNTER);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2 && !change_state |=> s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2);

  // 5: WAIT on transfer_complete deassert
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_5_WAIT && !transfer_complete |=> s_i2c_auto_init == AUTO_STATE_6_SEND_STOP_BIT);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_5_WAIT && transfer_complete |=> s_i2c_auto_init == AUTO_STATE_5_WAIT);

  // 6: SEND_STOP waits for transfer_complete assert
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_6_SEND_STOP_BIT && transfer_complete |=> s_i2c_auto_init == AUTO_STATE_7_INCREASE_COUNTER);
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_6_SEND_STOP_BIT && !transfer_complete |=> s_i2c_auto_init == AUTO_STATE_6_SEND_STOP_BIT);

  // 7: INCREASE_COUNTER -> 0
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_7_INCREASE_COUNTER |=> s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS);

  // 8: DONE holds
  assert property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_8_DONE |=> s_i2c_auto_init == AUTO_STATE_8_DONE);

  // Counter behavior and range
  assert property (@(posedge clk) reset |-> rom_address_counter == MIN_ROM_ADDRESS);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_7_INCREASE_COUNTER |-> rom_address_counter == $past(rom_address_counter) + 5'h1);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) != AUTO_STATE_7_INCREASE_COUNTER |-> rom_address_counter == $past(rom_address_counter));
  assert property (disable iff (reset) rom_address_counter <= MAX_ROM_ADDRESS);

  // Data_out mapping (registered on previous state)
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_1_SEND_START_BIT |-> data_out == 8'hBA);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_2_TRANSFER_BYTE_0 |-> data_out == rom_data[23:16]);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_0_CHECK_STATUS |-> data_out == rom_data[15:8]);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_3_TRANSFER_BYTE_1 |-> data_out == rom_data[15:8]);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_4_TRANSFER_BYTE_2 |-> data_out == rom_data[7:0]);

  // transfer_data behavior
  assert property (disable iff (reset) transfer_complete |-> transfer_data == 1'b0);
  assert property (disable iff (reset)
    ($past(s_i2c_auto_init) inside {AUTO_STATE_1_SEND_START_BIT, AUTO_STATE_2_TRANSFER_BYTE_0,
                                    AUTO_STATE_3_TRANSFER_BYTE_1, AUTO_STATE_4_TRANSFER_BYTE_2})
    && !transfer_complete |-> transfer_data == 1'b1);

  // send_start_bit behavior
  assert property (disable iff (reset) transfer_complete |-> send_start_bit == 1'b0);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_1_SEND_START_BIT && !transfer_complete |-> send_start_bit == 1'b1);

  // send_stop_bit behavior
  assert property (disable iff (reset) transfer_complete |-> send_stop_bit == 1'b0);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_6_SEND_STOP_BIT && !transfer_complete |-> send_stop_bit == 1'b1);

  // Error flag behavior
  assert property (@(posedge clk) reset |-> auto_init_error == 1'b0);
  assert property (@(posedge clk) clear_error |-> auto_init_error == 1'b0);
  assert property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_7_INCREASE_COUNTER && ack && !clear_error |-> auto_init_error == 1'b1);
  assert property (disable iff (reset)
    $past(auto_init_error) && !clear_error |-> auto_init_error);

  // Completion stickiness (derives from DONE hold)
  assert property (disable iff (reset) auto_init_complete |=> auto_init_complete);

  // Coverage
  cover property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS ##1
    s_i2c_auto_init == AUTO_STATE_1_SEND_START_BIT ##1
    s_i2c_auto_init == AUTO_STATE_2_TRANSFER_BYTE_0 ##1
    s_i2c_auto_init == AUTO_STATE_3_TRANSFER_BYTE_1 ##1
    s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2 ##1
    rom_data[24] ##1
    s_i2c_auto_init == AUTO_STATE_5_WAIT ##1
    s_i2c_auto_init == AUTO_STATE_6_SEND_STOP_BIT ##1
    s_i2c_auto_init == AUTO_STATE_7_INCREASE_COUNTER ##1
    s_i2c_auto_init == AUTO_STATE_0_CHECK_STATUS ##[0:$]
    s_i2c_auto_init == AUTO_STATE_8_DONE);

  cover property (disable iff (reset)
    s_i2c_auto_init == AUTO_STATE_4_TRANSFER_BYTE_2 && change_state && !rom_data[24] ##1
    s_i2c_auto_init == AUTO_STATE_7_INCREASE_COUNTER);

  cover property (disable iff (reset)
    $past(s_i2c_auto_init) == AUTO_STATE_7_INCREASE_COUNTER && ack && !clear_error ##1 auto_init_error);

  cover property (disable iff (reset) auto_init_complete);

endmodule