module top_module ( 
    input wire clk, 
    input wire reset_n, 
    input wire [7:0] in, 
    output wire [15:0] out );

    reg [7:0] in_reg;
    wire [15:0] sum;
    wire [7:0] out_vec;

    sum_module sum_inst (
        .in(in_reg),
        .out(sum)
    );

    always @(posedge clk) begin
        if (reset_n == 1'b0) begin
            in_reg <= 8'b0;
        end else begin
            in_reg <= in;
        end
    end

    assign out_vec = in_reg;
    assign out = {out_vec, sum};

endmodule

module sum_module (
    input wire [7:0] in, 
    output wire [15:0] out );

    assign out = {8'b0, in} + {in, 8'b0};

endmodule