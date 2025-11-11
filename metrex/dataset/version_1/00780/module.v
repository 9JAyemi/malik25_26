module top_module (
    input clk,
    input RST,
    input [3:0] a,
    input [3:0] b,
    input sub,
    input cin,
    input select,
    output reg cout,
    output reg overflow,
    output reg [7:0] q
);

reg [3:0] counter;
reg [3:0] adder_out;
reg [3:0] selected_out;

wire [3:0] adder_in;
assign adder_in = sub ? (a - b - cin) : (a + b + cin);

always @(posedge clk or negedge RST) begin
    if (!RST) begin
        counter <= 4'b0;
        adder_out <= 4'b0;
        selected_out <= 4'b0;
        cout <= 1'b0;
        overflow <= 1'b0;
        q <= 8'b0;
    end else begin
        counter <= counter + 1;
        adder_out <= adder_in;
        selected_out <= select ? adder_out : counter;
        {cout, q} <= selected_out + counter;
        overflow <= (selected_out[3] == counter[3]) && (selected_out[3] != q[3]);
    end
end

endmodule