
module traffic_light(
    input clk,
    input reset,
    input pedestrian_button,
    output reg red_light,
    output reg yellow_light,
    output reg green_light,
    output reg pedestrian_light
);

    // define state variables
    parameter IDLE = 2'b00;
    parameter TRAFFIC_LIGHT = 2'b01;
    parameter PEDESTRIAN_LIGHT = 2'b10;
    reg [1:0] state = IDLE;

    // define counters for each state
    reg [3:0] red_counter = 0;
    reg [2:0] yellow_counter = 0;
    reg [4:0] green_counter = 0;
    reg [3:0] pedestrian_counter = 0;

    always @(posedge clk) begin

        if(reset) begin
            // reset all counters and set state to idle
            red_counter <= 0;
            yellow_counter <= 0;
            green_counter <= 0;
            pedestrian_counter <= 0;
            state <= IDLE;
        end

        else begin
            case(state)

                IDLE: begin
                    // set traffic light to red and wait for 5 seconds
                    red_light <= 1;
                    yellow_light <= 0;
                    green_light <= 0;
                    pedestrian_light <= 0;
                    red_counter <= red_counter + 1;

                    if(red_counter == 5) begin
                        red_counter <= 0;
                        state <= TRAFFIC_LIGHT;
                    end
                end

                TRAFFIC_LIGHT: begin
                    // set traffic light to yellow and wait for 2 seconds
                    red_light <= 0;
                    yellow_light <= 1;
                    green_light <= 0;
                    pedestrian_light <= 0;
                    yellow_counter <= yellow_counter + 1;

                    if(yellow_counter == 2) begin
                        yellow_counter <= 0;
                        state <= PEDESTRIAN_LIGHT;
                    end
                end

                PEDESTRIAN_LIGHT: begin
                    // set pedestrian light to red and wait for 5 seconds
                    red_light <= 1;
                    yellow_light <= 0;
                    green_light <= 0;
                    pedestrian_light <= 1;
                    pedestrian_counter <= pedestrian_counter + 1;

                    if(pedestrian_counter == 5) begin
                        pedestrian_counter <= 0;
                        state <= IDLE;
                    end
                end

            endcase
        end
        // check for pedestrian button press
        if(pedestrian_button && state == IDLE) begin
            state <= PEDESTRIAN_LIGHT;
        end
    end
endmodule
