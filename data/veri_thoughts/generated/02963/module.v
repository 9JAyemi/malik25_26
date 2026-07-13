module fsm_traffic_light_control (
  input clock,
  input reset,
  input pedestrian_crossing_button,
  output reg green_light,
  output reg yellow_light,
  output reg red_light
);

  parameter S0 = 2'b00;
  parameter S1 = 2'b01;
  parameter S2 = 2'b10;
  parameter S3 = 2'b11;
  
  reg [1:0] state, next_state;
  
  always @(posedge clock) begin
    if (reset) begin
      state <= S0;
    end else begin
      state <= next_state;
    end
  end
  
  always @(*) begin
    case (state)
      S0: begin
        green_light <= 1;
        yellow_light <= 0;
        red_light <= 0;
        if (pedestrian_crossing_button) begin
          next_state <= S1;
        end else begin
          next_state <= S0;
        end
      end
      S1: begin
        green_light <= 0;
        yellow_light <= 1;
        red_light <= 0;
        next_state <= S2;
      end
      S2: begin
        green_light <= 0;
        yellow_light <= 0;
        red_light <= 1;
        next_state <= S3;
      end
      S3: begin
        green_light <= 0;
        yellow_light <= 1;
        red_light <= 0;
        next_state <= S0;
      end
      default: begin
        green_light <= 0;
        yellow_light <= 0;
        red_light <= 0;
        next_state <= S0;
      end
    endcase
  end
  
endmodule
