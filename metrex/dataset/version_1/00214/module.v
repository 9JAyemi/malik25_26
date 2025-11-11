module uart_transmitter (
  input clk,
  input rst,
  input [7:0] data_in,
  input start,
  output reg tx,
  output reg done
);

  reg [3:0] counter;
  reg [9:0] shift_reg;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      counter <= 4'b0;
      tx <= 1'b1;
      done <= 1'b0;
    end else begin
      if (start && counter == 4'b0) begin
        shift_reg <= {1'b1, data_in, 1'b0};
        counter <= 4'b0001;
        done <= 1'b0;
      end else if (counter != 4'b0) begin
        tx <= shift_reg[0];
        shift_reg <= {1'b1, shift_reg[9:1]};
        counter <= counter + 4'b0001;
        if (counter == 4'b1010) begin
          counter <= 4'b0;
          done <= 1'b1;
        end
      end
    end
  end
endmodule

module uart_receiver (
  input clk,
  input rst,
  input rx,
  output reg [7:0] data_out,
  output reg valid
);

  reg [3:0] counter;
  reg [9:0] shift_reg;
  reg waiting_for_start;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      counter <= 4'b0;
      waiting_for_start <= 1'b1;
      valid <= 1'b0;
    end else begin
      if (waiting_for_start) begin
        if (!rx) begin
          counter <= 4'b0001;
          waiting_for_start <= 1'b0;
        end
      end else begin
        counter <= counter + 4'b0001;
        if (counter == 4'b1010) begin
          shift_reg <= {rx, shift_reg[9:1]};
          data_out <= shift_reg[8:1];
          valid <= shift_reg[9];
          waiting_for_start <= 1'b1;
          counter <= 4'b0;
        end else begin
          shift_reg <= {rx, shift_reg[9:1]};
          valid <= 1'b0;
        end
      end
    end
  end
endmodule