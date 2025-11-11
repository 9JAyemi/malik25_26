module bcd_counter (
    input clk,
    input reset,   // Synchronous active-high reset
    output [3:1] ena,
    output [15:0] q);

    // Define states
    parameter IDLE = 2'b00;
    parameter INC_D1 = 2'b01;
    parameter INC_D2 = 2'b10;
    parameter INC_D3 = 2'b11;

    // Define internal signals
    reg [15:0] count;
    reg [1:0] state;

    // Output enable signals for upper three digits
    assign ena = {state[1], state[0], 1'b1};

    // State machine
    always @(posedge clk) begin
        if (reset) begin
            count <= 16'd0;
            state <= IDLE;
        end
        else begin
            case (state)
                IDLE: begin
                    count <= 16'd0;
                    state <= INC_D1;
                end
                INC_D1: begin
                    count <= count + 4'd1;
                    if (count[3:0] == 4'd10) begin
                        state <= INC_D2;
                    end
                end
                INC_D2: begin
                    count <= count + 4'd1;
                    if (count[7:4] == 4'd10) begin
                        state <= INC_D3;
                    end
                end
                INC_D3: begin
                    count <= count + 4'd1;
                    if (count[11:8] == 4'd10) begin
                        state <= IDLE;
                    end
                end
            endcase
        end
    end

    // Output BCD counter
    assign q = {count[15:12], count[11:8], count[7:4], count[3:0]};

endmodule