
module adder (input signed [7:0] A, input signed [7:0] B, output signed [7:0] sum, output reg C);

    wire signed [8:0] temp_sum;  // 8-bit wire to hold the intermediate sum
    assign temp_sum = A + B;    // Perform the addition

    assign sum = temp_sum[7:0]; // Extract the lower 8 bits as the sum

    always @(*) begin
        C = temp_sum[8];        // Capture the carry bit as C
    end

endmodule