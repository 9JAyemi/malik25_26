
module snoop_module(
    input clk,
    input reset,
    input [7:0] snoopa,
    input [7:0] snoopd,
    input snoopp,
    output reg snoopq,
    output snoopm
);

reg [7:0] prgram [0:255];

integer i;

always @(posedge clk) begin
    if (reset) begin
        snoopq <= 0;
        i <= 0;
    end else begin
        snoopq <= prgram[snoopa];
        if (snoopp) begin
            prgram[snoopa] <= snoopd;
        end
        if (i == 255) begin
            i <= 0;
        end else begin
            i <= i + 1;
        end
    end
end

assign snoopm = (i == 255);

endmodule