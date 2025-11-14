module traffic_light_controller (
  input clk,
  input button,
  output reg red,
  output reg yellow,
  output reg green
);

  // Define the state machine states
  parameter STATE_GREEN = 2'b00;
  parameter STATE_YELLOW = 2'b01;
  parameter STATE_RED = 2'b10;

  // Define the state machine signals
  reg [1:0] state;
  reg [3:0] counter;

  // Initialize the state machine
  always @ (posedge clk) begin
    if (button) begin
      state <= STATE_RED;
      counter <= 0;
    end else begin
      case (state)
        STATE_GREEN: begin
          if (counter == 10) begin
            state <= STATE_YELLOW;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
        STATE_YELLOW: begin
          if (counter == 2) begin
            state <= STATE_RED;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
        STATE_RED: begin
          if (counter == 10) begin
            state <= STATE_YELLOW;
            counter <= 0;
          end else begin
            counter <= counter + 1;
          end
        end
      endcase
    end
  end

  // Control the traffic light outputs based on the state machine state
  always @ (posedge clk) begin
    case (state)
      STATE_GREEN: begin
        green <= 1;
        yellow <= 0;
        red <= 0;
      end
      STATE_YELLOW: begin
        green <= 0;
        yellow <= 1;
        red <= 0;
      end
      STATE_RED: begin
        green <= 0;
        yellow <= 0;
        red <= 1;
      end
    endcase
  end

endmodule