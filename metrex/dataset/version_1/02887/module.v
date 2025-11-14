module byte_reverse (
    input [31:0] in,
    output [31:0] out
);

    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};

endmodule

module top_module (
    input [31:0] in,
    input [2:0] sel, 
    input [7:0] data0,
    input [7:0] data1,
    input [7:0] data2,
    input [7:0] data3,
    input [7:0] data4,
    input [7:0] data5,
    output [7:0] out
);

    wire [31:0] reversed_in;
    byte_reverse byte_reverse_inst (
        .in(in),
        .out(reversed_in)
    );

    wire [7:0] and_output;
    assign and_output = data0[1:0] & data1[1:0] & data2[1:0] & data3[1:0] & data4[1:0] & data5[1:0];

    wire [7:0] mux_output;
    assign mux_output = (sel == 0) ? data0 :
                        (sel == 1) ? data1 :
                        (sel == 2) ? data2 :
                        (sel == 3) ? data3 :
                        (sel == 4) ? data4 :
                        (sel == 5) ? data5 :
                        (sel == 6 || sel == 7) ? and_output :
                        8'b0;

    wire [7:0] add_output;
    assign add_output = reversed_in[7:0] + mux_output;

    assign out = add_output;

endmodule