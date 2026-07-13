
module up_counter (
    input clk,
    input reset,   // Synchronous active-high reset
    input ena,     // Synchronous active-high enable
    output wire [15:0] q);

    // Define states
    parameter IDLE = 2'b00;
    parameter COUNT = 2'b01;
    parameter COUNT_BY_TWO = 2'b10;

    // Define state register and next state logic
    reg [1:0] state, next_state;
    always @ (posedge clk) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Define output register and output logic
    reg [15:0] count_reg;
    always @ (posedge clk) begin
        if (reset) begin
            count_reg <= 16'd0;
        end else if (ena) begin
            case (state)
                IDLE: begin
                    count_reg <= 16'd0;
                end
                COUNT: begin
                    count_reg <= count_reg + 1;
                end
                COUNT_BY_TWO: begin
                    count_reg <= count_reg + 2;
                end
            endcase
        end
    end
    assign q = count_reg;  // Corrected to use non-blocking assignment

    // Define next state logic
    always @ (state, ena) begin
        case (state)
            IDLE: begin
                if (ena) begin
                    next_state = COUNT;
                end else begin
                    next_state = IDLE;
                end
            end
            COUNT: begin
                if (ena) begin
                    next_state = COUNT_BY_TWO;
                end else begin
                    next_state = IDLE;
                end
            end
            COUNT_BY_TWO: begin
                if (ena) begin
                    next_state = COUNT;
                end else begin
                    next_state = IDLE;
                end
            end
        endcase
    end

endmodule

module top_module (
    input clk,
    input reset,   // Synchronous active-high reset
    input ena,     // Synchronous active-high enable
    output wire [15:0] q);

    up_counter counter (
        .clk(clk),
        .reset(reset),
        .ena(ena),
        .q(q)
    );

endmodule
