module POR (
    input VDD,
    input CLK,
    input reset, 
    output reg RESET
);

parameter t = 10; // Number of clock cycles for the reset signal delay
parameter IDLE = 2'b00, DELAY = 2'b01, NORMAL = 2'b10, DEFAULT = 2'b11;

reg [1:0] state; // Removed the initialization from here
reg [31:0] counter; // Counter for delay

always @(posedge CLK or posedge reset) begin
    if (reset) begin
        state <= IDLE; // Set the state to IDLE on reset
        RESET <= 1'b1; // Assert the RESET signal initially
        counter <= 0; // Initialize the counter
    end
    else begin
        case (state)
            IDLE: begin
                RESET <= 1'b1; // Assert reset signal
                state <= DELAY; // Transition to the DELAY state
                counter <= 0;
            end
            DELAY: begin
                if (counter < t) begin
                    counter <= counter + 1;
                end else begin
                    RESET <= 1'b0; // De-assert reset signal after delay
                    state <= NORMAL; // Transition to the NORMAL state
                end
            end
            NORMAL: begin
                RESET <= 1'b0;
            end
            DEFAULT: begin
                state <= IDLE; // Transition back to the IDLE state for recovery
            end
            default: begin
                state <= DEFAULT; // Handle any undefined states
            end
        endcase
    end
end

endmodule
