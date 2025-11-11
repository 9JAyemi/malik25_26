
module Profibus (
  input clk,
  input rst,
  input [7:0] din_master,
  input [7:0] din_slave,
  output reg [7:0] dout_master,
  output reg [7:0] dout_slave,
  output status_master,
  output status_slave
);

  // Define communication protocol between master and slave
  reg [1:0] state_master;
  reg [1:0] state_slave;
  parameter IDLE = 2'b00;
  parameter SEND_CMD = 2'b01;
  parameter RECEIVE_DATA = 2'b10;
  parameter SEND_DATA = 2'b11;
  
  // Define communication lines between master and slave
  reg [7:0] cmd_master;
  reg [7:0] cmd_slave;
  reg [7:0] data_master;
  reg [7:0] data_slave;
  
  // Status signals to indicate idle state
  wire status_master_int;
  wire status_slave_int;
  assign status_master = (state_master == IDLE) ? 1'b1 : 1'b0;
  assign status_slave = (state_slave == IDLE) ? 1'b1 : 1'b0;
  
  // Master block
  always @(posedge clk) begin
    if (rst) begin
      state_master <= IDLE;
      dout_slave <= 8'b0;
    end else begin
      case (state_master)
        IDLE: begin
          if (din_master != 8'b0) begin
            cmd_master <= din_master;
            state_master <= SEND_CMD;
          end
        end
        SEND_CMD: begin
          dout_slave <= cmd_master;
          state_master <= RECEIVE_DATA;
        end
        RECEIVE_DATA: begin
          if (din_master != 8'b0) begin
            data_master <= din_master;
            state_master <= SEND_DATA;
          end
        end
        SEND_DATA: begin
          dout_slave <= data_master;
          state_master <= IDLE;
        end
      endcase
    end
  end
  
  // Slave block
  always @(posedge clk) begin
    if (rst) begin
      state_slave <= IDLE;
      dout_master <= 8'b0;
    end else begin
      case (state_slave)
        IDLE: begin
          if (din_slave != 8'b0) begin
            cmd_slave <= din_slave;
            state_slave <= RECEIVE_DATA;
          end
        end
        RECEIVE_DATA: begin
          dout_master <= cmd_slave;
          state_slave <= SEND_DATA;
        end
        SEND_DATA: begin
          if (din_slave != 8'b0) begin
            data_slave <= din_slave;
            state_slave <= IDLE;
          end
        end
      endcase
    end
  end
  
endmodule
