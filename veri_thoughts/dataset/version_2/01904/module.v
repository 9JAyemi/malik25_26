
module Mealy (
    input [n-1:0] in,      // n-bit input signal
    output reg [m-1:0] out,     // m-bit output signal
    input clk             // clock signal
);

parameter n = 4;          // number of input signals
parameter m = 2;          // number of output signals
parameter s = 3;          // number of states

reg [s-1:0] state;        // current state
reg [s-1:0] next_state;  // next state
reg [m-1:0] output_next; // next output

// State transition logic
always @(*) begin
    case (state)
        0: begin // State 0
            if (in[0] && in[1]) begin
                next_state = 1;
                output_next = {1'b1, 1'b0};
            end else begin
                next_state = 2;
                output_next = {1'b0, 1'b1};
            end
        end

        1: begin // State 1
            if (in[2]) begin
                next_state = 0;
                output_next = {1'b0, 1'b1};
            end else begin
                next_state = 2;
                output_next = {1'b0, 1'b0};
            end
        end

        2: begin // State 2
            if (in[3]) begin
                next_state = 0;
                output_next = {1'b1, 1'b1};
            end else begin
                next_state = 1;
                output_next = {1'b0, 1'b0};
            end
        end

        default: begin // Default state
            next_state = 0;
            output_next = {1'b0, 1'b0};
        end
    endcase
end

// State register
always @(posedge clk) begin
    state <= next_state;
end

// Output register
always @(posedge clk) begin
    out <= output_next;
end

endmodule