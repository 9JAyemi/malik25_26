```systemverilog
module mux_assertions (
    input logic CLK,
    input logic EN,
    input logic [1:0] SEL,
    input logic [3:0] ABCD,
    output logic Y
);
    // EN must be 1'b0 to drive Y LOW
    always_ff @(posedge CLK) begin
        disable iff (!EN) Y <= 1'b0;
    end

    // EN must be 1'b1 to drive Y from ABCD based on SEL
    always_ff @(posedge CLK) begin
        disable iff (!EN) case (SEL)
            2'b00: Y <= ABCD[0];
            2'b01: Y <= ABCD[1];
            2'b10: Y <= ABCD[2];
            2'b11: Y <= ABCD[3];
            default: Y <= 1'bx; // This case should not be reached due to EN being 1'b1
        endcase
    end

    // Y should be 1'bx when SEL is invalid and EN is 1'b1
    always_ff @(posedge CLK) begin
        disable iff (!EN) if (SEL != 2'b00 && SEL != 2'b01 && SEL != 2'b10 && SEL != 2'b11) Y <= 1'bx;
    end
endmodule
```