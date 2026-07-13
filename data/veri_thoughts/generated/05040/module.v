
module top_module (
    input clk,
    input slowena,     // Pause and resume counting signal
    input reset,       // Asynchronous reset
    input [1:0] a,     // 2-bit input for the decoder
    input [1:0] b,     // 2-bit input for the decoder
    output [7:0] q     // 8-bit output from the functional module
);

    // Decoder module
    wire [15:0] dec_out;
    decoder_4to16 dec_inst (
        .in(b),
        .out(dec_out)
    );

    // Counter module
    reg [3:0] count;
    always @(posedge clk or negedge reset) begin
        if (reset == 0) begin
            count <= 0;
        end else if (slowena == 1) begin
            count <= count + 1;
        end
    end

    // Functional module
    wire [3:0] dec_index;
    assign dec_index = dec_out[15:12];
    wire [3:0] count_index;
    assign count_index = count[3:0];
    wire [7:0] add_out;
    adder add_inst (
        .in1(dec_index),
        .in2(count_index),
        .out(add_out)
    );
    assign q = add_out;

endmodule
module decoder_4to16 (
    input [1:0] in,
    output [15:0] out
);

    assign out = 16'b0000000000000001 << {in[1], in[0]};

endmodule
module adder (
    input [3:0] in1,
    input [3:0] in2,
    output [7:0] out
);

    assign out = {4'b0, in1} + {4'b0, in2};

endmodule