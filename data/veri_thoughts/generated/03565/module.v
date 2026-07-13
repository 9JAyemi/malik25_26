module regSR #(
    parameter INIT = 1'bX,
    parameter SRMODE = 1'b0
) (
    input D,
    input CLK,
    input RST,
    output reg Q
);

    always @(posedge CLK or posedge RST) begin
        if (RST) begin
            Q <= INIT;
        end else if (SRMODE) begin
            Q <= ~Q;
        end else begin
            Q <= D;
        end
    end

endmodule