module bm_dag2_log_mod(
    input clock,
    input reset_n,
    input [1:0] a_in,
    input [1:0] b_in,
    input c_in,
    input d_in,
    output reg [1:0] out0,
    output reg out1
);

wire [1:0] temp_a;
wire [1:0] temp_b;
wire temp_c;
wire temp_d;

a top_a(clock, a_in, b_in, temp_a);
b top_b(clock, a_in, b_in, temp_b);

always @(posedge clock)
begin
    out0 <= temp_a & temp_b;
    out1 <= c_in & d_in;
end

endmodule

module a(
    input clock,
    input [1:0] a_in,
    input [1:0] b_in,
    output reg [1:0] out
);

always @(posedge clock)
begin
    out <= a_in & b_in;
end

endmodule

module b(
    input clock,
    input [1:0] a_in,
    input [1:0] b_in,
    output reg [1:0] out
);

always @(posedge clock)
begin
    out <= a_in | b_in;
end

endmodule