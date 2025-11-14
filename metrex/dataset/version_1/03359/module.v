
module data_converter (
    input [3:0] data_in,
    output [1:0] data_out
);

    assign data_out = (data_in <= 4) ? 2'b00 : 
                     (data_in <= 8) ? 2'b01 : 
                     (data_in <= 12) ? 2'b10 : 2'b11;

endmodule
