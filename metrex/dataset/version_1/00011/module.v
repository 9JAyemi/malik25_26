
module comparator (
    input [3:0] in1,
    input [3:0] in2,
    output reg out
);

always @(*) begin
    out = (in1 == in2);
end

endmodule

module shift_reg_comp (
    input clk,
    input reset,
    input load,
    input enable,
    input [3:0] data_in,
    output reg [3:0] out
);

wire comp_out;

comparator compare_unit (
    .in1(data_in),
    .in2(out),
    .out(comp_out)
);

always @(posedge clk) begin
    if (reset) begin
        out <= 4'b0;
    end else if (load) begin
        out <= data_in;
    end else if (enable) begin
        out <= data_in;
    end
end

endmodule
