module add_overflow_detection (
    input [7:0] a,
    input [7:0] b,
    output reg [7:0] s,
    output reg overflow
);

    reg [8:0] temp; // temporary variable to hold the sum
    
    always @(*) begin
        temp = a + b;
        if (temp > 127 || temp < -128) // check for signed overflow
            overflow <= 1;
        else
            overflow <= 0;
        s <= temp[7:0]; // truncate to 8 bits
    end
    
endmodule