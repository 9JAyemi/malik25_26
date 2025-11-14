module traffic_light_controller(
    input clk,
    input pedestrian_button,
    output reg red_light,
    output reg yellow_light,
    output reg green_light
);

reg [5:0] counter = 0; // 6-bit counter for 1 Hz clock
reg [3:0] pedestrian_counter = 0; // 4-bit counter for pedestrian crossing

always @(posedge clk) begin
    counter <= counter + 1;

    if (pedestrian_button) begin
        // Pedestrian crossing mode
        if (pedestrian_counter < 10) begin
            red_light <= 0;
            yellow_light <= 0;
            green_light <= 0;
            pedestrian_counter <= pedestrian_counter + 1;
        end else begin
            pedestrian_counter <= 0;
        end
    end else begin
        // Standard traffic light pattern
        if (counter < 20) begin
            red_light <= 0;
            yellow_light <= 0;
            green_light <= 1;
        end else if (counter < 25) begin
            red_light <= 0;
            yellow_light <= 1;
            green_light <= 0;
        end else if (counter < 45) begin
            red_light <= 1;
            yellow_light <= 0;
            green_light <= 0;
        end else begin
            counter <= 0;
        end
    end
end

endmodule