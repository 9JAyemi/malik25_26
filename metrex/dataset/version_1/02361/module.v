
module mux4_diff (
    input [3:0] I,
    input [1:0] S,
    output reg O,
    output reg OB
);

    // 4:1 MUX implementation
    always @(*) begin
        case (S)
            2'b00: begin
                O = I[0];
                OB = ~I[0];
            end
            2'b01: begin
                O = I[1];
                OB = ~I[1];
            end
            2'b10: begin
                O = I[2];
                OB = ~I[2];
            end
            2'b11: begin
                O = I[3];
                OB = ~I[3];
            end
        endcase
    end

endmodule