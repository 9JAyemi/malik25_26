module reg3_sync_reset (
    input CLK,
    input RST,
    input [2:0] D,
    output reg [2:0] Q
);

    always @(posedge CLK) begin
        if (RST) begin
            Q <= 0;
        end else begin
            Q <= D;
        end
    end
    
endmodule