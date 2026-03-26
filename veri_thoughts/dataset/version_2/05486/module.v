module bitwise_or (
    input [2:0] a,
    input [2:0] b,
    output [2:0] result
);
    assign result = a | b;
endmodule

module logical_or (
    input [2:0] a,
    input [2:0] b,
    output result
);
    assign result = (a != 0) || (b != 0);
endmodule

module accumulator (
    input clk,
    input rst_n,
    input [7:0] data_in,
    input valid,
    output reg [7:0] data_out
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'b0;
        end else if (valid) begin
            data_out <= data_out + data_in;
        end
    end
endmodule

module combiner (
    input [7:0] acc_data,
    input [2:0] bitwise_data,
    input logical_data,
    output [9:0] data_out
);
    assign data_out = {acc_data, bitwise_data, logical_data};
endmodule

module top_module (
    input clk,
    input rst_n,
    input [2:0] a,
    input [2:0] b,
    input [7:0] data_in,
    input valid_a,
    input ready_b,

    output ready_a,
    output reg valid_b,
    output reg [9:0] data_out
);
    wire [2:0] bitwise_result;
    wire logical_result;
    reg [7:0] acc_data;

    bitwise_or or1 (
        .a(a),
        .b(b),
        .result(bitwise_result)
    );

    logical_or or2 (
        .a(a),
        .b(b),
        .result(logical_result)
    );

    accumulator acc (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .valid(valid_a),
        .data_out(acc_data)
    );

    combiner comb (
        .acc_data(acc_data),
        .bitwise_data(bitwise_result),
        .logical_data(logical_result),
        .data_out(data_out)
    );

    assign ready_a = ready_b;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_b <= 1'b0;
        end else begin
            valid_b <= valid_a;
        end
    end
endmodule