
module traffic_light_controller (
  input clk,
  input areset,
  input pedestrian_button,
  output reg red_light,
  output reg yellow_light,
  output reg green_light,
  output reg walk_signal
);

  // Define the states
  parameter STATE_0 = 3'b000;
  parameter STATE_1 = 3'b001;
  parameter STATE_2 = 3'b010;
  parameter STATE_3 = 3'b011;
  parameter STATE_4 = 3'b100;

  // Define the current state
  reg [2:0] current_state, next_state;

  // State machine logic
  always @(posedge clk) begin
    if (areset == 1'b1) begin
      current_state <= STATE_0;
    end else begin
      current_state <= next_state;
    end
  end

  always @* begin
    case (current_state)
      STATE_0: begin
        if (pedestrian_button == 1'b1) begin
          next_state <= STATE_4;
        end else begin
          next_state <= STATE_1;
        end
      end
      STATE_1: begin
        next_state <= STATE_2;
      end
      STATE_2: begin
        next_state <= STATE_3;
      end
      STATE_3: begin
        next_state <= STATE_0;
      end
      STATE_4: begin
        next_state <= STATE_0;
      end
    endcase
  end

  // Output logic
  always @* begin
    case (current_state)
      STATE_0: begin
        red_light <= 1'b1;
        yellow_light <= 1'b0;
        green_light <= 1'b0;
        walk_signal <= 1'b0;
      end
      STATE_1: begin
        red_light <= 1'b1;
        yellow_light <= 1'b0;
        green_light <= 1'b0;
        walk_signal <= 1'b1;
      end
      STATE_2: begin
        red_light <= 1'b0;
        yellow_light <= 1'b1;
        green_light <= 1'b0;
        walk_signal <= 1'b0;
      end
      STATE_3: begin
        red_light <= 1'b0;
        yellow_light <= 1'b0;
        green_light <= 1'b1;
        walk_signal <= 1'b1;
      end
      STATE_4: begin
        red_light <= 1'b0;
        yellow_light <= 1'b1;
        green_light <= 1'b0;
        walk_signal <= 1'b1;
      end
    endcase
  end
endmodule