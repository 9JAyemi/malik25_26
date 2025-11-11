module multiplier (
    input wire clk,
    input wire [10:0] Q, // Multiplier
    input wire [10:0] Q_reg, // Multiplicand, loaded once and kept constant
    output reg [23:0] P // Product
);

    reg [10:0] multiplier;
    reg [21:0] multiplicand;
    reg [5:0] counter; // Counter to track the multiplication steps

    always @(posedge clk) begin
        if (counter == 0) begin // Initialization
            multiplier <= Q;
            multiplicand <= Q_reg;
            P <= 0;
            counter <= 11; // Set the counter for 11 cycles of multiplication
        end else begin
            if (multiplier[0]) // If the LSB of the multiplier is 1, add the multiplicand to the product
                P <= P + {multiplicand, 10'b0}; // Shift multiplicand to align with the current bit of multiplier
            
            // Shift the multiplicand and multiplier for the next bit
            multiplicand <= multiplicand << 1;
            multiplier <= multiplier >> 1;
            counter <= counter - 1;
        end
    end
endmodule
