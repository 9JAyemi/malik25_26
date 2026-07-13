module shifter (
    input [3:0] data_in,
    input rotate,
    output [3:0] data_out
);
    wire [3:0] shifted_data;
    
    assign shifted_data[0] = rotate ? data_in[3] : data_in[0];
    assign shifted_data[1] = rotate ? data_in[0] : data_in[1];
    assign shifted_data[2] = rotate ? data_in[1] : data_in[2];
    assign shifted_data[3] = rotate ? data_in[2] : data_in[3];
    
    assign data_out = shifted_data;
endmodule
module mux_4to1 (
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [1:0] select,
    output [3:0] out
);
    reg [3:0] mux_out;
    
    always @* begin
        case (select)
            2'b00: mux_out = data0;
            2'b01: mux_out = data1;
            2'b10: mux_out = data2;
            2'b11: mux_out = data3;
        endcase
    end
    
    assign out = mux_out;
endmodule
module top_module (
    input [3:0] data1,
    input rotate,
    input [3:0] data2,
    input [1:0] select,
    output [3:0] out
);
    wire [3:0] shifted_data;
    wire [3:0] mux_data;
    
    shifter shifter_inst (
        .data_in(data1),
        .rotate(rotate),
        .data_out(shifted_data)
    );
    
    mux_4to1 mux_inst (
        .data0(shifted_data),
        .data1(data2),
        .data2(4'b0),
        .data3(4'b1),
        .select(select),
        .out(mux_data)
    );
    
    assign out = mux_data;
endmodule
