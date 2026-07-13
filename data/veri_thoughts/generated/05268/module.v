module counter #(
    parameter HIGH = 1'b1,
    parameter LOW = 1'b0
)(
    input CLK,
    input RESET,
    input ENABLE,
    output reg [3:0] COUNT
);

always @(posedge CLK) begin
    if (RESET == HIGH) begin
        COUNT <= 4'b0;
    end else if (ENABLE == HIGH) begin
        COUNT <= COUNT + 1;
    end
end

endmodule