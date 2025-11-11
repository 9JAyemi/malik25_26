
module profibus_slave (
  input clk,
  input rst,
  input enable,
  input req,
  input [7:0] data_in,
  output ack,
  output [7:0] data_out
);

  reg [7:0] internal_data;

  always @(posedge clk) begin
    if (rst) begin
      internal_data <= 0;
    end else if (enable) begin
      if (req) begin
        internal_data <= data_in;
      end
    end
  end

  assign ack = enable & req;
  assign data_out = internal_data;

endmodule

module profibus_master (
  input clk,
  input rst,
  input enable,
  output reg req,
  input ack,
  output reg [7:0] data_out,
  input [7:0] data_in
);

  reg [7:0] internal_data;
  reg [2:0] state;

  parameter IDLE = 3'b000;
  parameter SEND_REQ = 3'b001;
  parameter WAIT_ACK = 3'b010;
  parameter READ_DATA = 3'b011;

  always @(posedge clk) begin
    if (rst) begin
      req <= 0;
      internal_data <= 0;
      state <= IDLE;
    end else if (enable) begin
      case (state)
        IDLE: begin
          req <= 0;
          if (data_in != 0) begin
            internal_data <= data_in;
            state <= SEND_REQ;
          end
        end
        SEND_REQ: begin
          req <= 1;
          state <= WAIT_ACK;
        end
        WAIT_ACK: begin
          if (ack) begin
            state <= READ_DATA;
          end
        end
        READ_DATA: begin
          data_out <= internal_data;
          state <= IDLE;
        end
      endcase
    end
  end

endmodule
