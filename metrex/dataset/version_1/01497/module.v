module binary_counter (
    input  wire        CLK,
    input  wire        RST,
    input  wire        COUNT_EN,
    output reg  [3:0]  Q
);

    always @(posedge CLK) begin
        if (RST) begin
            Q <= 4'b0000;
        end else if (COUNT_EN) begin
            Q <= Q + 1;
        end
    end

endmodule