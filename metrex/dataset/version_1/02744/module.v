
module Profibus (
  input wire clk,
  input wire rst,
  input wire [7:0] data_in,
  output wire [7:0] data_out,
  output wire enable,
  output wire busy
);

// Master block
wire [7:0] master_data_out;
wire [7:0] master_data_in;
wire master_enable;
wire master_busy;

// Slave block
wire [7:0] slave_data_in;
wire [7:0] slave_data_out;
wire slave_enable;
wire slave_busy;

// Communication protocol
reg [1:0] state;
parameter IDLE = 2'b00,
          SEND = 2'b01,
          RECEIVE = 2'b10;
assign enable = master_enable;
assign busy = master_busy;
assign data_out = slave_data_out;

// State machine
always @(posedge clk) begin
  if(rst) begin
    state <= IDLE;
  end else begin
    case(state)
      IDLE: begin if (enable) begin state <= SEND; end end
      SEND: begin if (~master_busy) begin state <= RECEIVE; end end
      RECEIVE: begin if (~slave_busy) begin state <= IDLE; end end
    endcase
  end
end

// Master block
assign master_data_out = (state == SEND) ? data_in : 8'b0;
assign master_enable = (state == SEND);
assign master_busy = (state == SEND || state == RECEIVE);
assign slave_data_in = master_data_out;

// Slave block
assign slave_data_out = (state == RECEIVE) ? master_data_out : 8'b0;
assign slave_enable = (state == RECEIVE);
assign slave_busy = (state == SEND || state == RECEIVE);

endmodule