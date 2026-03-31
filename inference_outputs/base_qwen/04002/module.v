module decoder (
    input A,
    input B,
    output reg [15:0] O
);

    // Implement 4-to-16 decoder using a case statement
    // If A and B are both 0, O0 should be high and all other outputs should be low
    // If A is 0 and B is 1, O1 should be high and all other outputs should be low
    // If A is 1 and B is 0, O2 should be high and all other outputs should be low
    // If A and B are both 1, O3 should be high and all other outputs should be low

    // Use case statement to assign output values
    // Default case is to set all outputs to 0
    always @* begin
        case ({A, B})
            2'b00: O = 16'b0000000000000001;
            2'b01: O = 16'b0000000000000010;
            2'b10: O = 16'b0000000000000100;
            2'b11: O = 16'b0000000000001000;
            default: O = 16'b0000000000000000;
        endcase
    end

endmodule