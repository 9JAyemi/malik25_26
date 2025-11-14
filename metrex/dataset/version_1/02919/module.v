
module traffic_controller(
    input clk, //clock signal
    input reset, //reset signal
    input pedestrian_button, //pedestrian crossing button
    output reg [1:0] traffic_light, //traffic light output (0 for red, 1 for yellow, 2 for green)
    output reg pedestrian_crossing //pedestrian crossing output (0 for not active, 1 for active)
);

reg [3:0] state; //state machine variable
reg [3:0] counter; //counter variable
parameter GREEN_TIME = 10; //green state time
parameter YELLOW_TIME = 2; //yellow state time
parameter RED_TIME = 8; //red state time
parameter CROSSING_TIME = 15; //pedestrian crossing time

//initialize state and counter variables
initial begin
    state = 4'b0100; //initial state is green for both lanes
    counter = 4'b0000; //initial counter value is 0
end

//state machine
always @(posedge clk or posedge reset) begin
    if(reset) begin
        state <= 4'b0100; //reset state to green for both lanes
        counter <= 4'b0000; //reset counter to 0
    end else begin
        case(state)
            4'b0100: begin //green state
                if(counter == GREEN_TIME) begin //green time is 10 seconds
                    state <= 4'b0010; //switch to yellow state
                    counter <= 4'b0000; //reset counter
                end else begin
                    counter <= counter + 1; //increment counter
                end
            end
            4'b0010: begin //yellow state
                if(counter == YELLOW_TIME) begin //yellow time is 2 seconds
                    state <= 4'b1000; //switch to red state
                    counter <= 4'b0000; //reset counter
                end else begin
                    counter <= counter + 1; //increment counter
                end
            end
            4'b1000: begin //red state
                if(counter == RED_TIME) begin //red time is 8 seconds
                    state <= 4'b0101; //switch to green state for other lane
                    counter <= 4'b0000; //reset counter
                end else if (pedestrian_button) begin //if pedestrian button is pressed, switch to pedestrian crossing state
                    state <= 4'b1001;
                    counter <= 4'b0000;
                end else begin //otherwise, increment counter
                    counter <= counter + 1;
                end
            end
            4'b0101: begin //green state for other lane
                if(counter == GREEN_TIME) begin //green time is 10 seconds
                    state <= 4'b0011; //switch to yellow state for other lane
                    counter <= 4'b0000; //reset counter
                end else begin
                    counter <= counter + 1; //increment counter
                end
            end
            4'b0011: begin //yellow state for other lane
                if(counter == YELLOW_TIME) begin //yellow time is 2 seconds
                    state <= 4'b1000; //switch to red state
                    counter <= 4'b0000; //reset counter
                end else begin
                    counter <= counter + 1; //increment counter
                end
            end
            4'b1001: begin //pedestrian crossing state
                if(counter == CROSSING_TIME) begin //pedestrian crossing time is 15 seconds
                    state <= 4'b1000; //switch back to red state
                    counter <= 4'b0000; //reset counter
                end else begin
                    counter <= counter + 1; //increment counter
                end
            end
        endcase
    end
end

//traffic light output
always @(state) begin
    case(state)
        4'b0100, 4'b1001: traffic_light <= 2'b10; //green state for lane 1, red state for lane 2
        4'b0010, 4'b0011: traffic_light <= 2'b01; //yellow state for both lanes
        4'b1000, 4'b0101: traffic_light <= 2'b00; //red state for lane 1, green state for lane 2
    endcase
end

//pedestrian crossing output
always @(state) begin
    case(state)
        4'b1001: pedestrian_crossing <= 1'b1; //active
        default: pedestrian_crossing <= 1'b0; //not active
    endcase
end

endmodule