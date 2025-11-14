module divider(
    input clk,
    input rst,
    input start,
    input [15:0] dividend,
    input [15:0] divisor,
    output reg [15:0] quotient,
    output reg [15:0] remainder,
    output reg busy,
    output reg valid
);

    reg [31:0] dividend_temp;
    reg [15:0] divisor_temp;
    reg [4:0] count;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            quotient <= 0;
            remainder <= 0;
            dividend_temp <= 0;
            divisor_temp <= 0;
            count <= 0;
            busy <= 0;
            valid <= 0;
        end else if (start && !busy) begin
            dividend_temp <= {16'b0, dividend};  // Load the dividend
            divisor_temp <= divisor;             // Load the divisor
            quotient <= 0;                       // Reset the quotient
            count <= 16;                         // Initialize the count
            busy <= 1;                           // Set the busy flag
            valid <= 0;                          // Clear the valid flag
        end else if (busy) begin
            if (count > 0) begin
                // Left shift dividend_temp and bring down the next bit of the dividend
                dividend_temp <= dividend_temp << 1;
                // Subtract the divisor from the dividend_temp, if possible
                if (dividend_temp[31:16] >= divisor) begin
                    dividend_temp[31:16] <= dividend_temp[31:16] - divisor_temp;
                    dividend_temp[0] <= 1'b1; // Set the LSB of dividend_temp as part of the quotient
                end
                count <= count - 1; // Decrement the count
            end else begin
                quotient <= dividend_temp[15:0];  // Final quotient
                remainder <= dividend_temp[31:16]; // Remainder
                busy <= 0;                        // Clear the busy flag
                valid <= 1;                       // Set the valid flag to indicate completion
            end
        end
    end

endmodule
