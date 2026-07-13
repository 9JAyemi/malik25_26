
module mux (
    input [3:0] ABCD,
    input [1:0] SEL,
    input EN,
    output reg Y
);

    always @ (ABCD, SEL, EN) begin
        if (EN == 1'b0) begin
            Y <= 1'b0;
        end else begin
            case (SEL)
                2'b00: Y <= ABCD[0];
                2'b01: Y <= ABCD[1];
                2'b10: Y <= ABCD[2];
                2'b11: Y <= ABCD[3];
                default: Y <= 1'bx; // Added default case to assign 'X' to Y for invalid SEL values
            endcase
        end
    end

endmodule
