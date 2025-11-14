module binary_counter (
    input clk,
    input reset,      // Asynchronous active-high reset
    input load,       // Active-high parallel load input
    input [3:0] load_value, // 4-bit load value
    output [3:0] q,
    output carry_out,
    output led);

    reg [3:0] q_next;   // Next state of the counter
    reg [3:0] q_reg;    // Current state of the counter

    assign q = q_reg;
    assign carry_out = (q_reg == 4'b1111) ? 1'b1 : 1'b0;   // Set carry_out high when counter reaches 15

    // Synchronous counter logic
    always @(posedge clk or negedge reset) begin
        if (reset == 1'b0) begin
            q_reg <= 4'b0101;   // Reset counter to 5
        end else if (load == 1'b1) begin
            q_reg <= load_value; // Load specific value when load input is high
        end else begin
            q_reg <= q_next;    // Update counter with next state
        end
    end

    // Combinational logic for next state of the counter
    always @(*) begin
        if (q_reg == 4'b1111) begin
            q_next = 4'b0000;   // If counter is at max value, reset to 0
        end else begin
            q_next = q_reg + 1; // Increment counter
        end
    end

    // LED control logic
    assign led = carry_out;

endmodule