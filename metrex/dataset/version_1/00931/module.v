module uart
  (
   input                      clk,
   input                      rst,  // Synchronous reset
   input                      rx,   // Data in
   output reg                 busy, // Goes high when receiving data
   output reg [7:0]           data  // Data output
   );

   parameter DATA_BITS = 8;
   parameter BAUD = 19200;
   parameter CLK_RATE = 100000000;
   localparam CLK_DIV = CLK_RATE / BAUD;

   reg [1:0] state = 2'b00;
   reg rx_reg = 1'b1;
   reg [$clog2(CLK_DIV)-1:0] baud_counter = 0;
   reg [$clog2(DATA_BITS)-1:0] rx_counter = 0;

   always @ (posedge clk) begin
      if (rst) begin
         state <= 2'b00;
         busy <= 1'b0;
         data <= 8'b0;
      end else begin
         case (state)
            2'b00: begin // STATE_IDLE
               if (~rx_reg) begin
                  busy <= 1'b1;
                  state <= 2'b01;
                  baud_counter <= 0;
                  rx_counter <= 0;
               end
            end
            2'b01: begin // STATE_WAIT_HALF
               if (baud_counter == (CLK_DIV / 2) - 1) begin
                  state <= 2'b10;
                  baud_counter <= 0;
               end else begin
                  baud_counter <= baud_counter + 1;
               end
            end
            2'b10: begin // STATE_RX
               if (baud_counter == CLK_DIV - 1) begin
                  data <= { rx_reg, data[7:1] }; // Sample the serial input
                  baud_counter <= 0;
                  if (rx_counter == DATA_BITS - 1) begin
                     state <= 2'b11;
                  end else begin
                     rx_counter <= rx_counter + 1;
                  end
               end else begin
                  baud_counter <= baud_counter + 1;
               end
            end
            2'b11: begin // STATE_END
               if (baud_counter == CLK_DIV - 1) begin
                  if (rx_reg) begin
                     busy <= 1'b0;
                     state <= 2'b00;
                  end
                  baud_counter <= 0;
               end else begin
                  baud_counter <= baud_counter + 1;
               end
            end
         endcase
         rx_reg <= rx;
      end
   end

endmodule