
module shift_register (
    input clk,
    input [3:0] data_in,
    output [3:0] data_out
);

    reg [3:0] q;
    
    always @(posedge clk) begin
        q <= {q[2:0], data_in[0]};
    end

    assign data_out = q;

endmodule