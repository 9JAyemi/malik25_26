module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [3:0] a, // 4-bit input A for the comparator
    input [3:0] b, // 4-bit input B for the comparator
    output reg out_func, // 1-bit output from the functional module
    output [2:0] count // 3-bit output from the counter
);

reg [2:0] counter;
wire equal;

comparator_4bit comp_inst (
    .a(a),
    .b(b),
    .equal(equal)
);

always @(posedge clk) begin
    if (reset) begin
        counter <= 3'b0;
    end else begin
        counter <= counter + 1;
    end
end

always @(posedge clk) begin
    if (counter > b) begin
        out_func <= 1'b1;
    end else begin
        out_func <= 1'b0;
    end
end

assign count = counter;

endmodule

module comparator_4bit (
    input [3:0] a,
    input [3:0] b,
    output reg equal
);

always @(a, b) begin
    if (a == b) begin
        equal <= 1'b1;
    end else begin
        equal <= 1'b0;
    end
end

endmodule