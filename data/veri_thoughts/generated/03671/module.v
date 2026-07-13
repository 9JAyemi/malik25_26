module counter (
    CLK,
    RST,
    EN,
    OUT
);

    input CLK;
    input RST;
    input EN;
    output reg [3:0] OUT;

    always @(posedge CLK or negedge RST)
    begin
        if (!RST) // asynchronous reset
            OUT <= 4'd0;
        else if (EN) // counter enabled
            OUT <= OUT + 1;
    end

endmodule