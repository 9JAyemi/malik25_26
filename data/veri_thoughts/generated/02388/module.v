
module twos_complement (
    input [3:0] in,
    output reg [3:0] out,
    input CLK
);

    wire [3:0] not_in;

    assign not_in = ~in;          
    always @(posedge CLK) begin
        out = not_in + 4'b0001; 
    end

endmodule