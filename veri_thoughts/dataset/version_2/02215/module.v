module comparator_generic (
    input [3:0] Ain,
    input [3:0] Bin,
    output reg [3:0] CompOut
);

    // Comparator logic
    always @ (Ain, Bin) begin
        // Initialize output
        CompOut = 4'b0000;

        // Check if Ain is equal to Bin
        if (Ain == Bin) begin
            CompOut[0] = 1'b1; // Ain equals Bin
        end
        else if (Ain > Bin) begin
            CompOut[1] = 1'b1; // Ain is greater than Bin
        end
        else begin
            CompOut[2] = 1'b1; // Ain is less than Bin
        end

        // CompOut[3] can be assigned another condition or left as 0
    end

endmodule
