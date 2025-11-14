module rising_edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] out
);

reg [7:0] prev_in;

always @(posedge clk) begin
    if (in > prev_in) begin
        out <= in;
    end
    prev_in <= in;
end

endmodule

module shift_register (
    input clk,
    input [7:0] in,
    output reg [7:0] out
);

reg [7:0] shift_reg;

always @(posedge clk) begin
    shift_reg <= {shift_reg[6:0], in};
    out <= shift_reg;
end

endmodule

module data_selector (
    input [7:0] in,
    input [7:0] stored,
    input [2:0] select,
    output reg [7:0] selected
);

always @(*) begin
    case (select)
        3'b000: selected = in;
        3'b001: selected = stored;
        default: selected = 8'b0;
    endcase
end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    input [2:0] select,
    output [7:0] q
);

wire [7:0] rising_edge_out;
wire [7:0] shift_reg_out;

rising_edge_detector red_inst (
    .clk(clk),
    .in(in),
    .out(rising_edge_out)
);

shift_register sr_inst (
    .clk(clk),
    .in(rising_edge_out),
    .out(shift_reg_out)
);

data_selector ds_inst (
    .in(in),
    .stored(shift_reg_out),
    .select(select),
    .selected(q)
);

endmodule