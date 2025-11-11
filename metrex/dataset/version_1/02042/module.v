
module parity_sum (
    input [7:0] a,
    input [7:0] b,
    output [8:0] parity_sum
);

endmodule
module parity_checker #(
    parameter DATAWIDTH = 8
) (
    input [DATAWIDTH-1:0] data,
    output parity
);

    wire [DATAWIDTH-1:0] sum;
    genvar i;
    
    for (i = 0; i < DATAWIDTH; i = i + 1) begin : adder_tree
        assign sum[i] = data[i] ^ (i == 0 ? 0 : sum[i-1]);
    end
    
    assign parity = sum[DATAWIDTH-1];

endmodule