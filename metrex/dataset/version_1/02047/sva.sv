// SVA for I2C. Bind this module to the DUT to tap internals.
module I2C_sva #(parameter int DELAY_P = 10)
(
  input  logic        SDA,
  input  logic        SCL,
  input  logic        rst,
  input  logic [2:0]  state,
  input  logic        ack,
  // internal taps
  input  logic [2:0]  current_state,
  input  logic        ack_reg,
  input  logic [3:0]  delay_counter,
  input  logic [2:0]  data_index,
  input  logic        start_condition,
  input  logic        sda_signal,
  input  logic        scl_signal
);

  localparam logic [2:0] IDLE  = 3'b000;
  localparam logic [2:0] START = 3'b001;
  localparam logic [2:0] WRITE = 3'b010;
  localparam logic [2:0] READ  = 3'b011;
  localparam logic [2:0] ACK_S = 3'b100;
  localparam logic [2:0] NACK_S= 3'b101;

  default clocking cb @(posedge SCL); endclocking
  default disable iff (rst);

  // Output mirrors internal regs
  assert property (state == current_state);
  assert property (ack   == ack_reg);

  // Valid state encoding
  assert property (state inside {IDLE,START,WRITE,READ,ACK_S,NACK_S});

  // Reset post-conditions on first clock after rst rises
  assert property ($rose(rst) |=> state==IDLE && ack==0 && sda_signal==1 && scl_signal==1
                                      && delay_counter==0 && data_index==3'b000);

  // IDLE gating
  assert property (state==IDLE && !start_condition |=> state==IDLE);
  assert property (state==IDLE &&  start_condition |=> state==START);

  // delay_counter behavior
  assert property (state inside {START,WRITE,ACK_S,NACK_S} |-> delay_counter <= DELAY_P);
  assert property (state inside {START,WRITE,ACK_S,NACK_S} && delay_counter <  DELAY_P
                   |=> delay_counter == $past(delay_counter)+1);
  assert property (state inside {START,WRITE,ACK_S,NACK_S} && delay_counter == DELAY_P
                   |=> delay_counter == 0);

  // START completion → WRITE side-effects
  assert property (state==START && delay_counter==DELAY_P
                   |=> state==WRITE && sda_signal==0 && scl_signal==0);

  // WRITE bit/phase progression
  assert property (state==WRITE && delay_counter==DELAY_P && data_index < 3'b100
                   |=> data_index == $past(data_index)+1);

  // WRITE completion → ACK/NACK selection and effects
  assert property (state==WRITE && delay_counter==DELAY_P && data_index==3'b100
                   |=> state inside {ACK_S,NACK_S} && data_index==3'b000 && ack == ~ $past(SDA));
  // Decision uses previous ack_reg (matches DUT behavior)
  assert property (state==WRITE && delay_counter==DELAY_P && data_index==3'b100
                   |=> (state==ACK_S) == $past(ack_reg));

  // Entering ACK/NACK starts with counter cleared
  assert property ($past(state)==WRITE && state inside {ACK_S,NACK_S} |-> delay_counter==0);

  // ACK/NACK duration and exit to IDLE, lines released
  assert property (state inside {ACK_S,NACK_S} && delay_counter==DELAY_P
                   |=> state==IDLE && sda_signal==1 && scl_signal==1 && delay_counter==0);

  // ACK/NACK: ack stable while in these states
  assert property (state inside {ACK_S,NACK_S} |=> $stable(ack));

  // IDLE keeps lines high
  assert property (state==IDLE |-> sda_signal==1 && scl_signal==1);

  // Legal transition adjacency
  assert property ($past(state)==IDLE   |-> state inside {IDLE,START});
  assert property ($past(state)==START  |-> state inside {START,WRITE});
  assert property ($past(state)==WRITE  |-> state inside {WRITE,ACK_S,NACK_S});
  assert property ($past(state)==ACK_S  |-> state inside {ACK_S,IDLE});
  assert property ($past(state)==NACK_S |-> state inside {NACK_S,IDLE});

  // Key coverage
  cover property (state==IDLE && start_condition
                  ##1 state==START
                  ##[1:DELAY_P+1] state==WRITE
                  ##[1:DELAY_P+1] state==ACK_S
                  ##[1:DELAY_P+1] state==IDLE);

  cover property (state==IDLE && start_condition
                  ##1 state==START
                  ##[1:DELAY_P+1] state==WRITE
                  ##[1:DELAY_P+1] state==NACK_S
                  ##[1:DELAY_P+1] state==IDLE);

endmodule

// Bind example (tap DUT internals). Adjust instance name/style as needed.
bind I2C I2C_sva #(.DELAY_P(DELAY)) I2C_sva_i (
  .SDA(SDA), .SCL(SCL), .rst(rst),
  .state(state), .ack(ack),
  .current_state(current_state),
  .ack_reg(ack_reg),
  .delay_counter(delay_counter),
  .data_index(data_index),
  .start_condition(start_condition),
  .sda_signal(sda_signal),
  .scl_signal(scl_signal)
);