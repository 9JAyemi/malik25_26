module traffic_light(
    input clk,
    input reset,
    input car_sensor_road1_lane1,
    input car_sensor_road1_lane2,
    input car_sensor_road2_lane1,
    input car_sensor_road2_lane2,
    input pedestrian_sensor,
    output reg [3:0] traffic_light_road1,
    output reg [3:0] traffic_light_road2,
    output reg pedestrian_light
);

parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;
parameter GREEN_TIME = 5, PEDESTRIAN_TIME = 10, YELLOW_TIME = 2;

reg [1:0] state;
reg [3:0] timer;
reg [1:0] current_road1_lane;
reg [1:0] current_road2_lane;

always @(posedge clk) begin
    if (reset) begin
        state <= S0;
        timer <= 0;
        current_road1_lane <= 2'b00;
        current_road2_lane <= 2'b00;
        traffic_light_road1 <= 4'b0100;
        traffic_light_road2 <= 4'b0100;
        pedestrian_light <= 1'b0;
    end else begin
        case (state)
            S0: begin
                if (timer == 0) begin
                    if (pedestrian_sensor) begin
                        state <= S1;
                        timer <= PEDESTRIAN_TIME;
                        pedestrian_light <= 1'b1;
                        traffic_light_road1 <= {2'b10, 2'b01};
                        traffic_light_road2 <= {2'b00, 2'b10};
                    end else if (car_sensor_road1_lane1 || car_sensor_road1_lane2) begin
                        state <= S1;
                        timer <= GREEN_TIME;
                        current_road1_lane <= 2'b01;
                        traffic_light_road1 <= {2'b10, 2'b01};
                        traffic_light_road2 <= {2'b00, 2'b10};
                    end else if (car_sensor_road2_lane1 || car_sensor_road2_lane2) begin
                        state <= S2;
                        timer <= YELLOW_TIME;
                        traffic_light_road1 <= {2'b10, 2'b00};
                        traffic_light_road2 <= {2'b01, 2'b00};
                    end
                end else begin
                    timer <= timer - 1;
                end
            end
            S1: begin
                if (timer == 0) begin
                    state <= S2;
                    timer <= YELLOW_TIME;
                    traffic_light_road1 <= {2'b10, 2'b00};
                    traffic_light_road2 <= {2'b01, 2'b00};
                end else begin
                    timer <= timer - 1;
                end
            end
            S2: begin
                if (timer == 0) begin
                    if (pedestrian_sensor) begin
                        state <= S3;
                        timer <= PEDESTRIAN_TIME;
                        pedestrian_light <= 1'b1;
                        traffic_light_road1 <= {2'b00, 2'b10};
                        traffic_light_road2 <= {2'b10, 2'b01};
                    end else if (car_sensor_road2_lane1 || car_sensor_road2_lane2) begin
                        state <= S3;
                        timer <= GREEN_TIME;
                        current_road2_lane <= 2'b01;
                        traffic_light_road1 <= {2'b00, 2'b10};
                        traffic_light_road2 <= {2'b10, 2'b01};
                    end else if (car_sensor_road1_lane1 || car_sensor_road1_lane2) begin
                        state <= S1;
                        timer <= YELLOW_TIME;
                        traffic_light_road1 <= {2'b10, 2'b01};
                        traffic_light_road2 <= {2'b00, 2'b10};
                    end
                end else begin
                    timer <= timer - 1;
                end
            end
            S3: begin
                if (timer == 0) begin
                    state <= S0;
                    timer <= YELLOW_TIME;
                    traffic_light_road1 <= {2'b01, 2'b00};
                    traffic_light_road2 <= {2'b01, 2'b00};
                    pedestrian_light <= 1'b0;
                end else begin
                    timer <= timer - 1;
                end
            end
        endcase
    end
end

endmodule