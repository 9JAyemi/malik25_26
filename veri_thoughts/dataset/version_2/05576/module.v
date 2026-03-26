module top_module (
    input clk,
    input up_down,
    input load,
    input en,
    input [3:0] data_in,
    output [3:0] final_output
);

wire [3:0] counter_out;
wire [3:0] gray_out;

up_down_counter_4bit udc (
    .clk(clk),
    .up_down(up_down),
    .load(load),
    .en(en),
    .data_in(data_in),
    .out(counter_out)
);

binary_to_gray_4bit btg (
    .B(counter_out),
    .G(gray_out)
);

functional_module fm (
    .counter_out(counter_out),
    .gray_out(gray_out),
    .final_output(final_output)
);

endmodule

module up_down_counter_4bit (
    input clk,
    input up_down,
    input load,
    input en,
    input [3:0] data_in,
    output reg [3:0] out
);
always @(posedge clk) begin
    if (en) begin
        if (load) begin
            out <= data_in;
        end else begin
            if (up_down) begin
                out <= out + 1;
            end else begin
                out <= out - 1;
            end
        end
    end
end
endmodule

module binary_to_gray_4bit (
    input [3:0] B,
    output reg [3:0] G
);
always @(*) begin
    G[3] = B[3];
    G[2] = B[3] ^ B[2];
    G[1] = B[2] ^ B[1];
    G[0] = B[1] ^ B[0];
end
endmodule

module functional_module (
    input [3:0] counter_out,
    input [3:0] gray_out,
    output reg [3:0] final_output
);
always @(*) begin
    final_output = counter_out ^ gray_out;
end
endmodule