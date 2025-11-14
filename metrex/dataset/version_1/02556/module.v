
module traffic_light_fsm (
  input clk,
  input reset,
  output reg red,
  output reg green,
  output reg yellow
);

  parameter RED = 2'b00, GREEN = 2'b01, YELLOW = 2'b10;
  reg [1:0] state, next_state;
  reg [3:0] count;

  always @(posedge clk) begin
    if (reset) begin
      state <= RED;
      count <= 0;
    end else begin
      state <= next_state;
      count <= count + 1;
    end
  end

  always @(*) begin
    case (state)
      RED: begin
        red <= 1;
        green <= 0;
        yellow <= 0;
        if (count == 5) begin
          next_state = GREEN;
        end else begin
          next_state = RED;
        end
      end

      GREEN: begin
        red <= 0;
        green <= 1;
        yellow <= 0;
        if (count == 10) begin
          next_state = YELLOW;
        end else begin
          next_state = GREEN;
        end
      end

      YELLOW: begin
        red <= 0;
        green <= 0;
        yellow <= 1;
        if (count == 2) begin
          next_state = RED;
        end else begin
          next_state = YELLOW;
        end
      end

      default: begin
        red <= 0;
        green <= 0;
        yellow <= 0;
        next_state = RED;
      end
    endcase
  end

endmodule