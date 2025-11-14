// SVA for Altera_UP_I2C_AV_Auto_Initialize
// Bindable, concise, and covers key behavior

module Altera_UP_I2C_AV_Auto_Initialize_sva
#(
  parameter MIN_ROM_ADDRESS = 6'h00,
  parameter MAX_ROM_ADDRESS = 6'h32
)
(
  input  logic        clk,
  input  logic        reset,
  input  logic        clear_error,
  input  logic        ack,
  input  logic        transfer_complete,

  input  logic [7:0]  data_out,
  input  logic        transfer_data,
  input  logic        send_start_bit,
  input  logic        send_stop_bit,

  input  logic        auto_init_complete,
  input  logic        auto_init_error,

  input  logic [2:0]  s_i2c_auto_init,
  input  logic [5:0]  rom_address_counter,
  input  logic [25:0] rom_data,

  input  logic        change_state,
  input  logic        finished_auto_init
);

  default clocking cb @(posedge clk); endclocking

  localparam AUTO_STATE_0_CHECK_STATUS   = 3'h0;
  localparam AUTO_STATE_1_SEND_START_BIT = 3'h1;
  localparam AUTO_STATE_2_TRANSFER_BYTE_1= 3'h2;
  localparam AUTO_STATE_3_TRANSFER_BYTE_2= 3'h3;
  localparam AUTO_STATE_4_WAIT           = 3'h4;
  localparam AUTO_STATE_5_SEND_STOP_BIT  = 3'h5;
  localparam AUTO_STATE_6_INCREASE_COUNTER=3'h6;
  localparam AUTO_STATE_7_DONE           = 3'h7;

  // Reset effects (checked on the cycle after reset is high)
  assert property (@(posedge clk) reset |=> s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS);
  assert property (@(posedge clk) reset |=> data_out==8'h00 && transfer_data==0 && send_start_bit==0 && send_stop_bit==0 && auto_init_error==0 && rom_address_counter==MIN_ROM_ADDRESS);

  // Basic invariants
  assert property (disable iff (reset) s_i2c_auto_init inside {3'h0,3'h1,3'h2,3'h3,3'h4,3'h5,3'h6,3'h7});
  assert property (disable iff (reset) auto_init_complete == (s_i2c_auto_init==AUTO_STATE_7_DONE));
  assert property (disable iff (reset) change_state == (transfer_complete && transfer_data));
  assert property (disable iff (reset) finished_auto_init == (rom_address_counter==MAX_ROM_ADDRESS));

  // FSM next-state checks
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && finished_auto_init |=> s_i2c_auto_init==AUTO_STATE_7_DONE);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && rom_data[25] |=> s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && !rom_data[25] |=> s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT && change_state |=> s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT && !change_state |=> s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1 && change_state |=> s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1 && !change_state |=> s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2 && change_state && rom_data[24]   |=> s_i2c_auto_init==AUTO_STATE_4_WAIT);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2 && change_state && !rom_data[24]  |=> s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2 && !change_state                 |=> s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_4_WAIT && !transfer_complete |=> s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_4_WAIT &&  transfer_complete |=> s_i2c_auto_init==AUTO_STATE_4_WAIT);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT &&  transfer_complete |=> s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT && !transfer_complete |=> s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT);

  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER |=> s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_7_DONE |=> s_i2c_auto_init==AUTO_STATE_7_DONE);

  // Data output mapping per state
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT |-> data_out==rom_data[23:16]);
  assert property (disable iff (reset) (s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS || s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1) |-> data_out==rom_data[15:8]);
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2 |-> data_out==rom_data[7:0]);

  // Command strobes and transfer_data behavior
  assert property (disable iff (reset) transfer_complete |-> (transfer_data==0 && send_start_bit==0 && send_stop_bit==0));

  assert property (disable iff (reset) (s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT) && !transfer_complete |-> send_start_bit==1);
  assert property (disable iff (reset) (s_i2c_auto_init!=AUTO_STATE_1_SEND_START_BIT) |-> send_start_bit==0);

  assert property (disable iff (reset) (s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT) && !transfer_complete |-> send_stop_bit==1);
  assert property (disable iff (reset) (s_i2c_auto_init!=AUTO_STATE_5_SEND_STOP_BIT) |-> send_stop_bit==0);

  assert property (disable iff (reset) (s_i2c_auto_init inside {AUTO_STATE_1_SEND_START_BIT,AUTO_STATE_2_TRANSFER_BYTE_1,AUTO_STATE_3_TRANSFER_BYTE_2}) && !transfer_complete |-> transfer_data==1);
  assert property (disable iff (reset) !(s_i2c_auto_init inside {AUTO_STATE_1_SEND_START_BIT,AUTO_STATE_2_TRANSFER_BYTE_1,AUTO_STATE_3_TRANSFER_BYTE_2}) |-> transfer_data==0);

  // Error flag behavior
  assert property (disable iff (reset) (s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER && ack && !clear_error) |=> auto_init_error);
  assert property (@(posedge clk) clear_error |=> !auto_init_error);
  assert property (disable iff (reset) $rose(auto_init_error) |-> $past(s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER && ack && !clear_error));
  assert property (disable iff (reset) auto_init_error && !clear_error |=> auto_init_error);

  // Counter behavior
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER |=> rom_address_counter==$past(rom_address_counter)+1);
  assert property (disable iff (reset) !(s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER) |-> $stable(rom_address_counter));
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_7_DONE |-> $stable(rom_address_counter));

  // Completion handshake
  assert property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && finished_auto_init |=> s_i2c_auto_init==AUTO_STATE_7_DONE && auto_init_complete);

  // Coverage
  cover property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && rom_data[25] ##1 s_i2c_auto_init==AUTO_STATE_1_SEND_START_BIT ##1 s_i2c_auto_init==AUTO_STATE_2_TRANSFER_BYTE_1 ##1 s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2);
  cover property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && !finished_auto_init && !rom_data[25] ##1 s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2);
  cover property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_3_TRANSFER_BYTE_2 && change_state && rom_data[24] ##1 s_i2c_auto_init==AUTO_STATE_4_WAIT ##1 !transfer_complete ##1 s_i2c_auto_init==AUTO_STATE_5_SEND_STOP_BIT ##1 transfer_complete ##1 s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER);
  cover property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_0_CHECK_STATUS && finished_auto_init ##1 s_i2c_auto_init==AUTO_STATE_7_DONE && auto_init_complete);
  cover property (disable iff (reset) s_i2c_auto_init==AUTO_STATE_6_INCREASE_COUNTER && ack ##1 auto_init_error ##[1:10] clear_error ##1 !auto_init_error);

endmodule

// Example bind (place in your TB or a package, after compiling the DUT)
// bind Altera_UP_I2C_AV_Auto_Initialize Altera_UP_I2C_AV_Auto_Initialize_sva
// #(.MIN_ROM_ADDRESS(MIN_ROM_ADDRESS), .MAX_ROM_ADDRESS(MAX_ROM_ADDRESS)) sva (
//   .clk(clk), .reset(reset), .clear_error(clear_error), .ack(ack), .transfer_complete(transfer_complete),
//   .data_out(data_out), .transfer_data(transfer_data), .send_start_bit(send_start_bit), .send_stop_bit(send_stop_bit),
//   .auto_init_complete(auto_init_complete), .auto_init_error(auto_init_error),
//   .s_i2c_auto_init(s_i2c_auto_init), .rom_address_counter(rom_address_counter), .rom_data(rom_data),
//   .change_state(change_state), .finished_auto_init(finished_auto_init)
// );