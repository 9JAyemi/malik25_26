
module shift_register(
    input clk,
    input load,
    input [63:0] data,
    output reg [63:0] q
);
    always @(posedge load) begin
        if (load) begin
            q <= data;
        end
    end
endmodule
