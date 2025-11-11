
module top_module (
    input CLK,
    input RESET,
    input LOAD,
    input [3:0] DATA,
    input [3:0] A,
    input [3:0] B,
    input mode,
    output final_output
);

reg [3:0] counter_out_reg;
wire [3:0] counter_out_next;
wire comparator_out;

counter counter_inst (
    .CLK(CLK),
    .RESET(RESET),
    .LOAD(LOAD),
    .DATA(DATA),
    .out(counter_out_next)
);

always @(posedge CLK) begin
    if (RESET) begin
        counter_out_reg <= 0;
    end else begin
        counter_out_reg <= counter_out_next;
    end
end

comparator comparator_inst (
    .A(A),
    .B(B),
    .mode(mode),
    .out(comparator_out)
);

assign final_output = comparator_out & (counter_out_reg == 9);

endmodule

module counter (
    input CLK,
    input RESET,
    input LOAD,
    input [3:0] DATA,
    output [3:0] out
);

reg [3:0] out_reg;

always @(posedge CLK) begin
    if (RESET) begin
        out_reg <= 0;
    end else if (LOAD) begin
        out_reg <= DATA;
    end else begin
        out_reg <= out_reg + 1;
    end
end

assign out = out_reg;

endmodule

module comparator (
    input [3:0] A,
    input [3:0] B,
    input mode,
    output out
);

wire A_eq_B, A_gt_B, A_lt_B, A_neq_B;

assign A_eq_B = (A == B);
assign A_gt_B = (A > B);
assign A_lt_B = (A < B);
assign A_neq_B = (A != B);

assign out = (mode == 2'b00) ? A_eq_B :
             (mode == 2'b01) ? A_gt_B :
             (mode == 2'b10) ? A_lt_B :
             (mode == 2'b11) ? A_neq_B :
             1'b0;

endmodule
