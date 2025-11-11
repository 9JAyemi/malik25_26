module top_module (
    input clk,
    input [3:0] data_in,
    input load,
    input EN,
    output [7:0] final_output
);

reg [3:0] data_out;
reg [3:0] COUNT;
wire [7:0] concat_output;

shift_register sr (
    .clk(clk),
    .data_in(data_in),
    .load(load),
    .data_out(data_out)
);

binary_counter bc (
    .clk(clk),
    .EN(EN),
    .RST(1'b0),
    .COUNT(COUNT)
);

functional_module fm (
    .data_out(data_out),
    .COUNT(COUNT),
    .final_output(concat_output)
);

assign final_output = concat_output;

endmodule

module shift_register (
    input clk,
    input [3:0] data_in,
    input load,
    output reg [3:0] data_out
);

always @(posedge clk) begin
    if (load) begin
        data_out <= data_in;
    end else begin
        data_out <= {data_out[2:0], 1'b0};
    end
end

endmodule

module binary_counter (
    input clk,
    input EN,
    input RST,
    output reg [3:0] COUNT
);

always @(posedge clk or negedge RST) begin
    if (!RST) begin
        COUNT <= 4'b0000;
    end else if (EN) begin
        COUNT <= COUNT + 1;
    end
end

endmodule

module functional_module (
    input [3:0] data_out,
    input [3:0] COUNT,
    output reg [7:0] final_output
);

always @(data_out or COUNT) begin
    final_output <= {COUNT, data_out};
end

endmodule