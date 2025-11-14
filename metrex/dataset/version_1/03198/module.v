module traffic_light_control (
  input clk,
  input reset,
  output reg red,
  output reg yellow,
  output reg green
);

  parameter GREEN_TIME = 30;
  parameter YELLOW_TIME = 5;
  parameter RED_TIME = 25;
  
  reg [3:0] state;
  reg [5:0] counter;
  
  always @(posedge clk) begin
    if (reset) begin
      state <= 3'b001;
      counter <= 0;
    end else begin
      case (state)
        3'b001: begin // Green state
          green <= 1;
          yellow <= 0;
          red <= 0;
          if (counter == GREEN_TIME * 2) begin
            state <= 3'b010;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
        3'b010: begin // Yellow state
          green <= 0;
          yellow <= 1;
          red <= 0;
          if (counter == YELLOW_TIME * 2) begin
            state <= 3'b100;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
        3'b100: begin // Red state
          green <= 0;
          yellow <= 0;
          red <= 1;
          if (counter == RED_TIME * 2) begin
            state <= 3'b001;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
      endcase
    end
  end

endmodule
