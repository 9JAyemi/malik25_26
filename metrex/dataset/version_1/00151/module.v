module dff_with_reset (
    input D,
    input CLK,
    input RST,
    output reg Q
);

    always @(posedge CLK, posedge RST)
    begin
        if (RST) // asynchronous reset
            Q <= 0;
        else // clocked behavior
            Q <= D;
    end

endmodule