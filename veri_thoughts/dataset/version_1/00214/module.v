
module sync_resettable_latch(
    input [3:0] D,
    input EN,
    input RST,
    input CLK,
    output reg [3:0] Q
);

always @(posedge CLK) begin
    if (EN) begin
        Q <= D;
    end else if (RST) begin
        Q <= 4'b0;
    end
end

endmodule