module traffic_light_controller(
  input reset,
  input clk,
  output reg green,
  output reg yellow,
  output reg red
);

  // Define the state machine states
  parameter green_state = 2'b00;
  parameter yellow_state = 2'b01;
  parameter red_state = 2'b10;

  // Define the state machine signals
  reg [1:0] state;
  reg [5:0] counter;

  // Initialize the state machine
  always @ (posedge clk, posedge reset) begin
    if (reset) begin
      state <= green_state;
      counter <= 0;
    end else begin
      case (state)
        green_state: begin
          counter <= counter + 1;
          if (counter == 30) begin
            state <= yellow_state;
            counter <= 0;
          end
        end
        yellow_state: begin
          counter <= counter + 1;
          if (counter == 5) begin
            state <= red_state;
            counter <= 0;
          end
        end
        red_state: begin
          counter <= counter + 1;
          if (counter == 25) begin
            state <= green_state;
            counter <= 0;
          end
        end
      endcase
    end
  end

  // Set the output signals based on the current state
  always @ (state) begin
    case (state)
      green_state: begin
        green <= 1;
        yellow <= 0;
        red <= 0;
      end
      yellow_state: begin
        green <= 0;
        yellow <= 1;
        red <= 0;
      end
      red_state: begin
        green <= 0;
        yellow <= 0;
        red <= 1;
      end
    endcase
  end

endmodule