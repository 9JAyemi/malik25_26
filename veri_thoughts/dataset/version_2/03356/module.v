
module usb_controller #(
  parameter data_width = 8, // width of data bus
  parameter addr_width = 8 // width of address bus
) (
  input clk,
  input rst,
  input usb_in,
  input [data_width-1:0] data_in,
  input [addr_width-1:0] addr_in,
  output usb_out,
  output reg [data_width-1:0] data_out,
  output reg [addr_width-1:0] addr_out,
  output reg tx_en,
  input tx_done,
  input rx_en,
  output reg rx_done
);

parameter type = 0; // type of USB controller block

// State machine states
reg [1:0] state;
localparam idle = 2'b00, tx = 2'b01, rx = 2'b10, done = 2'b11;

always @(posedge clk or posedge rst) begin
  if (rst) begin
    state <= idle;
    data_out <= 0;
    addr_out <= 0;
    tx_en <= 0;
    rx_done <= 0;
  end else begin
    case (state)
      idle: begin
        if (type == 0 || type == 1) begin
          if (tx_done) begin
            state <= tx;
            data_out <= data_in;
            addr_out <= addr_in;
            tx_en <= 1;
          end
        end
        if (type == 2 || type == 1) begin
          if (rx_en) begin
            state <= rx;
            rx_done <= 0;
          end
        end
      end
      tx: begin
        if (tx_done) begin
          state <= done;
          tx_en <= 0;
        end
      end
      rx: begin
        if (usb_in) begin
          data_out <= usb_in;
          addr_out <= addr_in;
          state <= done;
          rx_done <= 1;
        end
      end
      done: begin
        state <= idle;
      end
    endcase
  end
end

assign usb_out = (state == tx) ? data_out :
                 (state == rx) ? usb_in : 1'b0;

endmodule