module timebase #(parameter integer n = 12, parameter integer value = 0)
(
    input clock,
    input reset,
    input enable,
    output reg tick,
    output reg [n-1:0] count_value
);

always @(posedge clock, posedge reset) begin
    if (reset == 1'b1) begin
        count_value <= value;
        tick <= 1'b0;
    end
    else if (enable == 1'b1) begin
        count_value <= count_value + 1;
        tick <= 1'b1;
    end
    else begin
        tick <= 1'b0;
    end
end

endmodule