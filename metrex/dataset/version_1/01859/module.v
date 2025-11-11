module TrafficLightController (
    input clk,
    input rst,
    output reg [1:0] state
);

localparam GREEN_TIME = 20;
localparam YELLOW_TIME = 5;
localparam RED_TIME = 15;

reg [5:0] counter;

always @(posedge clk or posedge rst) begin
    if (rst) begin
        counter <= 0;
        state <= 2'b01; // Green state
    end else begin
        counter <= counter + 1;
        case (state)
            2'b01: // Green state
                if (counter >= GREEN_TIME) begin
                    state <= 2'b10; // Yellow state
                    counter <= 0;
                end
            2'b10: // Yellow state
                if (counter >= YELLOW_TIME) begin
                    state <= 2'b11; // Red state
                    counter <= 0;
                end
            2'b11: // Red state
                if (counter >= RED_TIME) begin
                    state <= 2'b01; // Green state
                    counter <= 0;
                end
        endcase
    end
end

endmodule