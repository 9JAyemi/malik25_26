// SVA for lin_transmitter
// Bind as: bind lin_transmitter lin_transmitter_sva lin_transmitter_sva_i (.*);

module lin_transmitter_sva (
  input clk,
  input rst,
  input [7:0] tx_data,
  input tx_en,
  input tx,

  input [3:0] state,
  input [7:0] id,
  input [7:0] data,
  input parity,
  input [3:0] bit_count,
  input start_bit,
  input stop_bit,
  input tx_data_reg
);

  localparam [3:0] IDLE       = 4'b0000;
  localparam [3:0] SYNC_BREAK = 4'b0001;
  localparam [3:0] SYNC_FIELD = 4'b0010;
  localparam [3:0] DATA_FIELD = 4'b0011;
  localparam [3:0] STOP_BITS  = 4'b0100;

  default clocking cb @(posedge clk); endclocking

  // Reset values (note: tx_data_reg/tx end up 1 due to final assignment in DUT)
  assert property (@cb rst |-> state==IDLE && id==8'h00 && data==8'h00 &&
                            bit_count==4'd0 && start_bit==1'b0 && stop_bit==1'b0 &&
                            parity==1'b0 && tx_data_reg==1'b1 && tx==1'b1);

  // From here, disable on reset
  default disable iff (rst);

  // Structural consistency
  assert property (@cb tx == tx_data_reg);

  // IDLE behavior
  assert property (@cb (state==IDLE && !tx_en) |=> state==IDLE);
  // Handshake loads and transition to SYNC_BREAK
  assert property (@cb (state==IDLE && tx_en)
                   |=> (state==SYNC_BREAK && start_bit &&
                        id == $past(tx_data) &&
                        data[7:1] == $past(tx_data[6:0]) &&
                        data[0] == $past(parity)));

  // start_bit pulse and origin
  assert property (@cb start_bit |=> !start_bit);
  assert property (@cb start_bit |-> $past(state==IDLE && tx_en));

  // id/data only change on handshake
  assert property (@cb !(state==IDLE && tx_en) |=> $stable(id) && $stable(data));

  // State transition waypoints (as coded)
  assert property (@cb (state==SYNC_BREAK && bit_count==4'd3) |=> state==SYNC_FIELD);
  assert property (@cb (state==SYNC_FIELD && bit_count==4'd8) |=> state==DATA_FIELD);
  assert property (@cb (state==DATA_FIELD && bit_count==4'd9) |=> state==STOP_BITS);
  assert property (@cb (state==STOP_BITS  && bit_count==4'd2) |=> state==IDLE);

  // stop_bit semantics
  assert property (@cb $rose(stop_bit) |-> $past(bit_count)==4'd9);
  assert property (@cb $rose(stop_bit) |=> (bit_count==4'd0 && !stop_bit));

  // bit_count behavior
  assert property (@cb (state!=IDLE && !$past(stop_bit)) |-> bit_count == $past(bit_count)+1);
  assert property (@cb (state==IDLE) |-> $stable(bit_count));

  // Parity only updates on start_bit cycles
  assert property (@cb !$past(start_bit) |-> parity == $past(parity));

  // Final assignment dominance on tx_data_reg (as coded)
  assert property (@cb (state inside {SYNC_FIELD,DATA_FIELD,STOP_BITS}) |-> (tx_data_reg==1'b0 && tx==1'b0));
  assert property (@cb (state inside {IDLE,SYNC_BREAK})                |-> (tx_data_reg==1'b1 && tx==1'b1));

  // Coverage

  // Full frame: handshake to return to IDLE with a stop_bit pulse and bit_count reset
  cover property (@cb (state==IDLE && tx_en)
                       ##1 state==SYNC_BREAK
                       ##[1:16] state==SYNC_FIELD
                       ##[1:16] state==DATA_FIELD
                       ##[1:16] $rose(stop_bit)
                       ##1 state==STOP_BITS
                       ##[1:8] state==IDLE && bit_count==4'd0);

  // Observe id/data load on start
  cover property (@cb (state==IDLE && tx_en)
                       ##1 (id==$past(tx_data) && data[7:1]==$past(tx_data[6:0])));

  // See tx forced low in active states (per final assignment)
  cover property (@cb (state inside {SYNC_FIELD,DATA_FIELD,STOP_BITS}) && (tx==1'b0));

endmodule

bind lin_transmitter lin_transmitter_sva lin_transmitter_sva_i (.*);