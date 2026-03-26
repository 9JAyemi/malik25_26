
module mux_4to1_enable (
    input [3:0] in,
    input [1:0] sel,
    input enable,
    output reg out
);

    always @(*) 
        out = (enable & in[sel]);

endmodule