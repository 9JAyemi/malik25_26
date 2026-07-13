module top_module (
    input [1:0] sel,
    input [7:0] data0,
    input [7:0] data1,
    input [7:0] data2,
    input [7:0] data3,
    output reg [7:0] out
);

    wire [7:0] mux_out;
    wire [15:0] mult_out;
    
    mux_4to1 mux_inst (
        .sel(sel),
        .in0(data0),
        .in1(data1),
        .in2(data2),
        .in3(data3),
        .out(mux_out)
    );
    
    multiplier mult_inst (
        .in1(mux_out),
        .in2(8'b11111111),
        .out(mult_out)
    );
    
    always @(*) begin
        out <= mult_out[7:0];
    end

endmodule

module mux_4to1 (
    input [1:0] sel,
    input [7:0] in0,
    input [7:0] in1,
    input [7:0] in2,
    input [7:0] in3,
    output reg [7:0] out
);
    
    always @(*) begin
        case(sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            2'b11: out = in3;
        endcase
    end

endmodule

module multiplier (
    input [7:0] in1,
    input [7:0] in2,
    output reg [15:0] out
);
    
    always @(*) begin
        out = in1 * in2;
    end

endmodule