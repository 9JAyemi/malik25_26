module traffic_light(clk, reset, ped_cross, green, yellow, red, ped_red, ped_green);
  input clk, reset, ped_cross;
  output reg green, yellow, red, ped_red, ped_green;
  
  parameter GREEN_TIME = 500_000_000; // 10 seconds
  parameter YELLOW_TIME = 100_000_000; // 2 seconds
  parameter RED_TIME = 500_000_000; // 10 seconds
  
  reg [2:0] state = 3'b001; // initial state
  
  reg [29:0] green_count = 0; // counter for green light
  reg [29:0] yellow_count = 0; // counter for yellow light
  reg [29:0] red_count = 0; // counter for red light
  reg [29:0] ped_red_count = 0; // counter for pedestrian red light
  reg [29:0] ped_green_count = 0; // counter for pedestrian green light
  
  always @(posedge clk)
  begin
    if (reset)
      begin
        state <= 3'b001;
        green_count <= 0;
        yellow_count <= 0;
        red_count <= 0;
        ped_red_count <= 0;
        ped_green_count <= 0;
        green <= 1'b1;
        yellow <= 1'b0;
        red <= 1'b0;
        ped_red <= 1'b0;
        ped_green <= 1'b0;
      end
    else
      begin
        case (state)
          3'b001: // green light
            begin
              green_count <= green_count + 1;
              if (green_count == GREEN_TIME)
                begin
                  state <= 3'b010;
                  yellow_count <= 0;
                  green_count <= 0;
                  green <= 1'b0;
                  yellow <= 1'b1;
                end
            end
          3'b010: // yellow light
            begin
              yellow_count <= yellow_count + 1;
              if (yellow_count == YELLOW_TIME)
                begin
                  state <= 3'b011;
                  red_count <= 0;
                  yellow_count <= 0;
                  yellow <= 1'b0;
                  red <= 1'b1;
                end
            end
          3'b011: // red light
            begin
              red_count <= red_count + 1;
              if (ped_cross)
                begin
                  state <= 3'b101;
                  ped_red_count <= 0;
                  red_count <= 0;
                  red <= 1'b0;
                  ped_red <= 1'b1;
                end
              else if (red_count == RED_TIME)
                begin
                  state <= 3'b001;
                  green_count <= 0;
                  red_count <= 0;
                  red <= 1'b0;
                  green <= 1'b1;
                end
            end
          3'b101: // pedestrian red light
            begin
              ped_red_count <= ped_red_count + 1;
              if (ped_red_count == RED_TIME)
                begin
                  state <= 3'b110;
                  ped_red_count <= 0;
                  ped_green_count <= 0;
                  ped_red <= 1'b0;
                  ped_green <= 1'b1;
                end
            end
          3'b110: // pedestrian green light
            begin
              ped_green_count <= ped_green_count + 1;
              if (ped_green_count == GREEN_TIME)
                begin
                  state <= 3'b111;
                  ped_green_count <= 0;
                  ped_green <= 1'b0;
                  ped_red <= 1'b1;
                end
            end
          3'b111: // pedestrian red light
            begin
              ped_red_count <= ped_red_count + 1;
              if (ped_red_count == RED_TIME)
                begin
                  state <= 3'b001;
                  green_count <= 0;
                  ped_red_count <= 0;
                  ped_red <= 1'b0;
                  green <= 1'b1;
                end
            end
        endcase
      end
  end
endmodule