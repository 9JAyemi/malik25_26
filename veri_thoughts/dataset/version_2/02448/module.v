
module mux4x1(data0, data1, data2, data3, selectinput, out);
    input [15:0] data0, data1, data2, data3;
    input [1:0] selectinput;
    output [15:0] out;

    assign out = (selectinput[1]) ? ((selectinput[0]) ? data3 : data2) : ((selectinput[0]) ? data1 : data0);

endmodule