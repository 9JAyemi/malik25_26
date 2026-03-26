
module johnson_counter (
    input wire clk,
    input wire rst_n,
    output reg [7:0] out_vec
);

reg [7:0] state;

always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
        state <= 8'b00000000;
    end else begin
        state <= {state[6:0], state[7]};
    end
end

always @* begin
    case(state)
        8'b00000000: out_vec = 8'b00000000;
        8'b10000000: out_vec = 8'b10000000;
        8'b11000000: out_vec = 8'b11000000;
        8'b11100000: out_vec = 8'b11100000;
        8'b11110000: out_vec = 8'b11110000;
        8'b01111000: out_vec = 8'b01111000;
        8'b00111100: out_vec = 8'b00111100;
        8'b00011110: out_vec = 8'b00011110;
        8'b00001111: out_vec = 8'b00001111;
        default: out_vec = 8'b00000000;
    endcase
end

endmodule
module binary_number_module (
    input wire [3:0] in_vec,
    output reg [3:0] out_vec,
    output reg msb_out,
    output reg mid_out,
    output reg lsb_out
);

wire [3:0] temp_vec;

assign temp_vec = in_vec;

always @* begin
    out_vec = temp_vec;
    msb_out = temp_vec[3];
    mid_out = temp_vec[2];
    lsb_out = temp_vec[1];
end

endmodule
module functional_module (
    input wire [7:0] in_vec_1,
    input wire [3:0] in_vec_2,
    output reg [7:0] out_vec
);

always @* begin
    out_vec = in_vec_1 | {4'b0000, in_vec_2};
end

endmodule
module top_module ( 
    input wire clk, 
    input wire rst_n, 
    input wire [3:0] in_vec, 
    output wire [7:0] out_vec, 
    output wire msb_out, 
    output wire mid_out, 
    output wire lsb_out 
);

wire [7:0] jc_out;
wire [3:0] bn_out;
wire bn_msb_out;
wire bn_mid_out;
wire bn_lsb_out;

johnson_counter jc_inst (
    .clk(clk),
    .rst_n(rst_n),
    .out_vec(jc_out)
);

binary_number_module bn_inst (
    .in_vec(in_vec),
    .out_vec(bn_out),
    .msb_out(bn_msb_out),
    .mid_out(bn_mid_out),
    .lsb_out(bn_lsb_out)
);

functional_module fm_inst (
    .in_vec_1(jc_out),
    .in_vec_2(bn_out),
    .out_vec(out_vec)
);

assign msb_out = bn_msb_out;
assign mid_out = bn_mid_out;
assign lsb_out = bn_lsb_out;

endmodule