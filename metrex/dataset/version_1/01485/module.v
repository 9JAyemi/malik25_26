
module shift_left_module (
    input [99:0] in,
    input [5:0] shift_amount,
    output [99:0] out
);
    assign out = {in[shift_amount-1:0], {94{1'b0}}, in[99:shift_amount]};
endmodule
module accumulator (
    input [7:0] data_in,
    input clk,
    input rst_n,
    output [7:0] accum_out
);
    reg [7:0] accum_reg;

    always @(posedge clk or negedge rst_n) begin
        if (~rst_n) begin
            accum_reg <= 8'b0;
        end
        else begin
            accum_reg <= accum_reg + data_in;
        end
    end
    assign accum_out = accum_reg;
endmodule
module sum_module (
    input [99:0] shift_out,
    input [7:0] accum_out,
    input select,
    output [107:0] out
);
    assign out = {shift_out, accum_out};
endmodule
module top_module (
    input clk,
    input rst_n,
    input [99:0] in,
    input [5:0] shift_amount,
    input [7:0] data_in,
    input valid_a,
    input ready_b,
    input select,
    output ready_a,
    output valid_b,
    output [107:0] out
);
    wire [99:0] shift_out;
    wire [7:0] accum_out;

    shift_left_module shift_left_inst (
        .in(in),
        .shift_amount(shift_amount),
        .out(shift_out)
    );

    accumulator accum_inst (
        .data_in(data_in),
        .clk(clk),
        .rst_n(rst_n),
        .accum_out(accum_out)
    );

    sum_module sum_inst (
        .shift_out(shift_out),
        .accum_out(accum_out),
        .select(select),
        .out(out)
    );

    assign ready_a = ~valid_a | valid_b;
    assign valid_b = ready_b;
endmodule