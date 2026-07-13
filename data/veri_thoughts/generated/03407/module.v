
module binary_splitter (
    input [2:0] vec,
    output [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

assign {o2, o1, o0} = vec;
assign outv = vec;

endmodule

module binary_counter (
    input clk,
    input reset,
    output reg [3:0] q
);

always @(posedge clk) begin
    if (reset) begin
        q <= 4'b0000;
    end else begin
        q <= q + 1;
    end
end

endmodule

module control_logic (
    input select,
    input [2:0] vec,
    input clk,
    input reset,
    output [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

wire [2:0] splitter_outv;
wire splitter_o2;
wire splitter_o1;
wire splitter_o0;
wire [3:0] counter_q;

binary_splitter splitter(.vec(vec), .outv(splitter_outv), .o2(splitter_o2), .o1(splitter_o1), .o0(splitter_o0));
binary_counter counter(.clk(clk), .reset(reset), .q(counter_q));

assign outv = select ? splitter_outv : 3'b000;
assign o2 = select ? splitter_o2 : 1'b0;
assign o1 = select ? splitter_o1 : 1'b0;
assign o0 = select ? splitter_o0 : 1'b0;

endmodule

module top_module ( 
    input clk,
    input reset,
    input select,
    input [2:0] vec,
    output [2:0] outv,
    output wire o2,
    output wire o1,
    output wire o0
);

control_logic control(.select(select), .vec(vec), .clk(clk), .reset(reset), .outv(outv), .o2(o2), .o1(o1), .o0(o0));

endmodule
