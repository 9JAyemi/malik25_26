module bcd_counter (
    input clk,
    input reset,
    output [2:0] ena,
    output reg [15:0] q
);

reg [3:0] count;
reg [3:0] bcd_count;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        count <= 0;
        bcd_count <= 0;
    end else begin
        count <= count + 1;
        if (count == 4'b1010) begin
            count <= 0;
            bcd_count <= bcd_count + 1;
        end
    end
end

assign ena = bcd_count[2:0];

always @* begin
    case (count)
        4'b0000: q = {4'b0000, bcd_count};
        4'b0001: q = {4'b0001, bcd_count};
        4'b0010: q = {4'b0010, bcd_count};
        4'b0011: q = {4'b0011, bcd_count};
        4'b0100: q = {4'b0100, bcd_count};
        4'b0101: q = {4'b0101, bcd_count};
        4'b0110: q = {4'b0110, bcd_count};
        4'b0111: q = {4'b0111, bcd_count};
        4'b1000: q = {4'b1000, bcd_count};
        4'b1001: q = {4'b1001, bcd_count};
        default: q = 16'b0;
    endcase
end

endmodule