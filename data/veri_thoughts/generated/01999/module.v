module mux4to1 (
    input [3:0] data0x,
    input [3:0] data1x,
    input [3:0] data2x,
    input [3:0] data3x,
    input [1:0] sel,
    output [3:0] result
);

wire [3:0] selected_data;

assign selected_data = (sel == 2'b00) ? data0x :
                       (sel == 2'b01) ? data1x :
                       (sel == 2'b10) ? data2x :
                                        data3x ;

assign result = selected_data;

endmodule