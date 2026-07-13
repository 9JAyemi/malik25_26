
module barrel_shifter(
    input [15:0] in,    // 16-bit input to be split
    output reg [7:0] out1,    // 8-bit output 1
    output reg [7:0] out2    // 8-bit output 2
);

    always @(*) begin
        out1 = in[7:0];
        out2 = in[15:8];
    end

endmodule
module d_flip_flop(
    input clk,    // clock signal
    input d,    // data input
    output reg q    // output
);

    always @(posedge clk) begin
        q <= d;
    end

endmodule
module final_module(
    input clk,    // clock signal for the D flip-flop
    input [15:0] in,    // 16-bit input for the barrel shifter
    output reg [15:0] out    // 16-bit final output
);

    wire [7:0] out1;
    wire [7:0] out2;

    barrel_shifter bs(
        .in(in),
        .out1(out1),
        .out2(out2)
    );

    d_flip_flop ff(
        .clk(clk),
        .d(out1[7] & out2[0]),
        .q(out[0])
    );
    
    always @(*) begin
        out = {out1, out2, out[0]};
    end

endmodule