module decade_counter (
    input clk,
    input slowena,
    input reset,
    output reg [3:0] q);

    // Define states
    parameter IDLE = 2'b00;
    parameter COUNT = 2'b01;
    parameter PAUSE = 2'b10;

    // Define state register and next state logic
    reg [1:0] state, next_state;
    always @ (posedge clk) begin
        if (reset) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end

    // Define output logic
    always @ (state) begin
        case (state)
            IDLE: q <= 4'b0000;
            COUNT: q <= q + 1;
            PAUSE: q <= q;
        endcase
    end

    // Define next state logic
    always @ (state, slowena) begin
        case (state)
            IDLE: if (!slowena) begin
                     next_state = COUNT;
                  end else begin
                     next_state = IDLE;
                  end
            COUNT: if (q == 4'b1001) begin
                      next_state = IDLE;
                   end else if (slowena) begin
                      next_state = PAUSE;
                   end else begin
                      next_state = COUNT;
                   end
            PAUSE: if (!slowena) begin
                      next_state = COUNT;
                   end else begin
                      next_state = PAUSE;
                   end
        endcase
    end

endmodule

module top_module (
    input clk,
    input slowena,
    input reset,
    output [3:0] q);

    // Instantiate the decade counter module
    decade_counter dc (
        .clk(clk),
        .slowena(slowena),
        .reset(reset),
        .q(q)
    );

endmodule