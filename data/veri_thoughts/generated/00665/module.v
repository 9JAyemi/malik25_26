
module fsm_consecutive_ones_detection (
  input clk,
  input reset,
  input [15:0] data,
  output reg [3:0] count
);

  parameter S0 = 2'b00;
  parameter S1 = 2'b01;

  reg [1:0] state;
  reg [3:0] count_reg;

  always @(posedge clk) begin
    if (reset) begin
      state <= S0;
      count_reg <= 0;
    end else begin
      case (state)
        S0: begin
          if (data == 16'hFFFF) begin
            state <= S1;
            count_reg <= 1;
          end else begin
            state <= S0;
            count_reg <= 0;
          end
        end
        S1: begin
          if (data == 16'hFFFF) begin
            state <= S1;
            count_reg <= count_reg + 1;
          end else begin
            state <= S0;
            count_reg <= 0;
          end
        end
      endcase
    end
  end

  always @(*) begin
    if (state == S0) begin
      count = 0;
    end else begin
      count = count_reg;
    end
  end

endmodule