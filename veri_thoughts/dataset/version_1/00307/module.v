module complement (
    input D,
    output reg Q,
    input CLK
);

    reg reg1 = 0;
    reg reg2 = 1;

    always @(posedge CLK) begin
        reg1 <= D;
    end

    always @(posedge CLK) begin
        reg2 <= reg1;
    end

    always @(posedge CLK) begin
        Q <= reg1;
        reg2 <= ~reg2;
    end

endmodule