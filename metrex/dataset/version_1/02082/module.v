module fsm_traffic_light_control (
  input clk,
  input reset,
  input ped,
  output reg red,
  output reg green,
  output reg yellow
);

  parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10;
  reg [1:0] state, next_state;

  localparam red_time = 4;
  localparam green_time = 6;
  localparam yellow_time = 2;

  reg [2:0] counter;

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= S0;
      counter <= 0;
    end
    else begin
      state <= next_state;
      case (state)
        S0: begin
          counter <= red_time;
        end
        S1: begin
          if (ped) begin
            counter <= yellow_time;
          end
          else begin
            counter <= green_time;
          end
        end
        S2: begin
          counter <= yellow_time;
        end
        default: begin
          counter <= 0;
        end
      endcase
    end
  end

  always @(posedge clk) begin
    if (reset) begin
      red <= 1'b1;
      green <= 1'b0;
      yellow <= 1'b0;
    end
    else begin
      case (state)
        S0: begin
          red <= 1'b1;
          green <= 1'b0;
          yellow <= 1'b0;
        end
        S1: begin
          if (ped) begin
            red <= 1'b0;
            green <= 1'b0;
            yellow <= 1'b1;
          end
          else begin
            red <= 1'b0;
            green <= 1'b1;
            yellow <= 1'b0;
          end
        end
        S2: begin
          red <= 1'b0;
          green <= 1'b0;
          yellow <= 1'b1;
        end
        default: begin
          red <= 1'b0;
          green <= 1'b0;
          yellow <= 1'b0;
        end
      endcase
    end
  end

  always @(*) begin
    case (state)
      S0: begin
        next_state = S1;
      end
      S1: begin
        if (counter == 0) begin
          next_state = S2;
        end
        else begin
          next_state = S1;
        end
      end
      S2: begin
        if (counter == 0) begin
          next_state = S0;
        end
        else begin
          next_state = S2;
        end
      end
      default: begin
        next_state = S0;
      end
    endcase
  end

endmodule
