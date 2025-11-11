module fsm_example (
    input clk,           // Clock input
    input rst_n,         // Active low reset
    input next_state,    // Input to trigger the next state
    output reg [1:0] state_out // Output representing the current state
);

// State encoding
localparam S0 = 2'b00,
           S1 = 2'b01,
           S2 = 2'b10,
           S3 = 2'b11;

// Internal state register
reg [1:0] current_state, next_state_reg;

// State transition logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        current_state <= S0; // Reset to state S0
    end else begin
        current_state <= next_state_reg; // Move to the next state
    end
end

// Next state logic
always @(*) begin
    case (current_state)
        S0: next_state_reg = next_state ? S1 : S0;
        S1: next_state_reg = next_state ? S2 : S1;
        S2: next_state_reg = next_state ? S3 : S2;
        S3: next_state_reg = next_state ? S0 : S3;
        default: next_state_reg = S0;
    endcase
end

// Output logic
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state_out <= 2'b00; // Reset output
    end else begin
        state_out <= current_state; // Output the current state
    end
end

endmodule
