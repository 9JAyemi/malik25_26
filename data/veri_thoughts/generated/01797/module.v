module traffic_light_controller (
  input clk,
  input reset,
  output reg green_led,
  output reg yellow_led,
  output reg red_led
);

  // Define states and their corresponding values
  parameter GREEN = 2'b00;
  parameter YELLOW = 2'b01;
  parameter RED = 2'b10;

  // Define state register and initialize to GREEN
  reg [1:0] state = GREEN;

  // Define counter for each state
  reg [3:0] green_counter = 0;
  reg [1:0] yellow_counter = 0;
  reg [4:0] red_counter = 0;

  // Define state transitions and counter values
  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= GREEN;
      green_counter <= 0;
      yellow_counter <= 0;
      red_counter <= 0;
    end else begin
      case (state)
        GREEN: begin
          if (green_counter == 10) begin
            state <= YELLOW;
            green_counter <= 0;
            yellow_counter <= 0;
            red_counter <= 0;
          end else begin
            green_counter <= green_counter + 1;
          end
        end
        YELLOW: begin
          if (yellow_counter == 2) begin
            state <= RED;
            green_counter <= 0;
            yellow_counter <= 0;
            red_counter <= 0;
          end else begin
            yellow_counter <= yellow_counter + 1;
          end
        end
        RED: begin
          if (red_counter == 15) begin
            state <= GREEN;
            green_counter <= 0;
            yellow_counter <= 0;
            red_counter <= 0;
          end else begin
            red_counter <= red_counter + 1;
          end
        end
      endcase
    end
  end

  // Define output logic based on state
  always @(state) begin
    case (state)
      GREEN: begin
        green_led <= 1;
        yellow_led <= 0;
        red_led <= 0;
      end
      YELLOW: begin
        green_led <= 0;
        yellow_led <= 1;
        red_led <= 0;
      end
      RED: begin
        green_led <= 0;
        yellow_led <= 0;
        red_led <= 1;
      end
    endcase
  end

endmodule
