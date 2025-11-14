module my_RAM64X1D2_top (
    input clk,
    input [7:0] din,
    input we,
    input [5:0] addr,
    output [7:0] dout
);

wire [7:0] dout_a, dout_b;
wire [5:0] addr_a, addr_b;

assign addr_a = addr[5:0];
assign addr_b = {1'b0, addr[5:1]};

my_RAM64X1D2  ram_b (
    .clk(clk),
    .din(din),
    .dout(dout_b),
    .we(we),
    .addr(addr_b)
);

my_RAM64X1D2 ram_a (
    .clk(clk),
    .din(din),
    .dout(dout_a),
    .we(we),
    .addr(addr_a)
);

assign dout = {dout_a[0], dout_b[0]};

endmodule

module my_RAM64X1D2 (
    input clk,
    input [7:0] din,
    output reg [7:0] dout,
    input we,
    input [5:0] addr
);

reg [7:0] mem [0:63];

always @(posedge clk) begin
    if (we) begin
        mem[addr] <= din;
    end
    dout <= mem[addr];
end

endmodule