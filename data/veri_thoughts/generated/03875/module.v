
module dff (
    input  wire D,
    input  wire RST,
    input  wire SET,
    input  wire CLK,
    output reg  Q
);

    always @(posedge CLK) begin
        if (RST) begin
            Q <= 1'b0;
        end else if (SET) begin
            Q <= 1'b1;
        end else begin
            Q <= D;
        end
    end

endmodule