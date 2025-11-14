
module pulse_generator(
    input clk,
    input reset,
    input in,
    output reg p,
    output reg l
);

    reg [18:0] r;
    reg [1:0] state;
    parameter IDLE = 2'b00, COUNTING = 2'b01, PULSE = 2'b10;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            r <= 0;
            l <= 0;
            state <= IDLE;
        end else begin
            case(state)
                IDLE: begin
                    if (in) begin
                        state <= COUNTING;
                        r <= 0;
                        l <= 1;
                    end else begin
                        l <= 0;
                    end
                end
                COUNTING: begin
                    if (r == 250000) begin
                        state <= PULSE;
                        r <= 0;
                        p <= 1;
                    end else begin
                        r <= r + 1;
                        l <= 1;
                        p <= 0;
                    end
                end
                PULSE: begin
                    if (in) begin
                        state <= COUNTING;
                        r <= 0;
                        p <= 0;
                        l <= 1;
                    end else begin
                        l <= 0;
                        p <= 1;
                    end
                end
            endcase
        end
    end

endmodule