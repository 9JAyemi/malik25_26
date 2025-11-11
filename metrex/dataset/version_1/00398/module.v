module top_module (
    input clk,
    input rst,
    input up_down,
    input [7:0] data_in,
    output [7:0] output_sum
);

    wire [7:0] shift_reg_out;
    wire [3:0] counter_out;
    wire [7:0] shift_reg_counter_sum;

    shift_register shift_reg (
        .clk(clk),
        .rst(rst),
        .load(data_in),
        .shift_en(!up_down),
        .data_out(shift_reg_out)
    );

    up_down_counter counter (
        .clk(clk),
        .rst(rst),
        .up_down(up_down),
        .data_out(counter_out)
    );

    assign shift_reg_counter_sum = shift_reg_out + counter_out;

    assign output_sum = shift_reg_counter_sum;

endmodule

module shift_register (
    input clk,
    input rst,
    input [7:0] load,
    input shift_en,
    output reg [7:0] data_out
);

    always @(posedge clk) begin
        if (rst) begin
            data_out <= 8'b0;
        end else if (shift_en) begin
            data_out <= {data_out[6:0], 1'b0};
        end else begin
            data_out <= load;
        end
    end

endmodule

module up_down_counter (
    input clk,
    input rst,
    input up_down,
    output reg [3:0] data_out
);

    always @(posedge clk) begin
        if (rst) begin
            data_out <= 4'b0;
        end else if (up_down) begin
            data_out <= data_out + 1;
        end else begin
            data_out <= data_out - 1;
        end
    end

endmodule