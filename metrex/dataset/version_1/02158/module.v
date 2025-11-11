
module decade_counter (
    input clk,
    input pause,
    input resume,
    input reset,
    output reg [3:0] q
);

    // Define states
    parameter [2:0] COUNT_0 = 3'b000;
    parameter [2:0] COUNT_1 = 3'b001;
    parameter [2:0] COUNT_2 = 3'b010;
    parameter [2:0] COUNT_3 = 3'b011;
    parameter [2:0] COUNT_4 = 3'b100;
    parameter [2:0] COUNT_5 = 3'b101;
    parameter [2:0] COUNT_6 = 3'b110;
    parameter [2:0] COUNT_7 = 3'b111;

    // Define signals
    reg [2:0] state;
    reg [3:0] next_q;

    // Default output
    always @* begin
        q = next_q;
    end

    // State machine
    always @(posedge clk, posedge reset) begin
        if (reset) begin
            state <= COUNT_0;
            next_q <= 4'b0000;
        end else begin
            if (pause == 1'b0) begin
                case (state)
                    COUNT_0: begin
                        next_q <= 4'b0001;
                        state <= COUNT_1;
                    end
                    COUNT_1: begin
                        next_q <= 4'b0010;
                        state <= COUNT_2;
                    end
                    COUNT_2: begin
                        next_q <= 4'b0011;
                        state <= COUNT_3;
                    end
                    COUNT_3: begin
                        next_q <= 4'b0100;
                        state <= COUNT_4;
                    end
                    COUNT_4: begin
                        next_q <= 4'b0101;
                        state <= COUNT_5;
                    end
                    COUNT_5: begin
                        next_q <= 4'b0110;
                        state <= COUNT_6;
                    end
                    COUNT_6: begin
                        next_q <= 4'b0111;
                        state <= COUNT_7;
                    end
                    COUNT_7: begin
                        next_q <= 4'b1000;
                        state <= COUNT_0;
                    end
                endcase
            end
            if(resume == 1'b1)
                state <= state + 1;
        end
    end

endmodule
module top_module (
    input clk,
    input pause,
    input resume,
    input reset,
    output [3:0] q
);

    // Instantiate decade counter
    decade_counter counter (
        .clk(clk),
        .pause(pause),
        .resume(resume),
        .reset(reset),
        .q(q)
    );

endmodule