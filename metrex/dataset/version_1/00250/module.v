
module counter (
    input clk,
    input reset,
    input direction,
    output reg [2:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 3'b000;
    end else if (direction) begin
        count <= count + 1;
    end else if (!direction) begin
        count <= count - 1;
    end
end

endmodule
module comparator (
    input [3:0] a,
    input [3:0] b,
    output wire equal
);

assign equal = (a == b);

endmodule
module final_output (
    input [2:0] count,
    input equal,
    output reg [2:0] out_final
);

always @(*) begin
    if (equal) begin
        out_final = count;
    end else begin
        out_final = 3'b000;
    end
end

endmodule
module top_module (
    input clk,
    input reset,
    input direction,
    input [3:0] a,
    input [3:0] b,
    output [2:0] count,
    output wire equal,
    output [2:0] out_final
);

counter counter_inst (
    .clk(clk),
    .reset(reset),
    .direction(direction),
    .count(count)
);

comparator comparator_inst (
    .a(a),
    .b(b),
    .equal(equal)
);

final_output final_output_inst (
    .count(count),
    .equal(equal),
    .out_final(out_final)
);

endmodule