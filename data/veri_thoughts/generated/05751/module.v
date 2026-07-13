
module altpriority_encoder_6_3_lh (
    input [5:0] data,
    output reg [2:0] q
);

// Logic to implement the 6-to-3 priority encoder with least-hot encoding

always @(*) begin
    case (data)
        6'b000001: q = 3'b000;
        6'b000010: q = 3'b001;
        6'b000100: q = 3'b010;
        6'b001000: q = 3'b011;
        6'b010000: q = 3'b100;
        6'b100000: q = 3'b101;
        default: q = 3'b110; // Default encoding for unused inputs
    endcase
end

endmodule
