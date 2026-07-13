module dffe #(
    parameter SIZE = 8
)(
    input [SIZE-1:0] din,
    input en,
    input clk,
    output reg [SIZE-1:0] q,
    input se,
    input [SIZE-1:0] si,
    output [SIZE-1:0] so
);

    always @ (posedge clk) begin
        if (se) begin
            q <= si;
        end else if (en) begin
            q <= din;
        end
    end
    
    assign so = q;
    
endmodule