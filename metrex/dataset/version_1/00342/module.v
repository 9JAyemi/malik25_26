
module up_down_counter (
    input  wire        clk,
    input  wire        up_down,
    input  wire        load,
    input  wire        reset,
    input  wire [3:0]    data_in,
    output wire [3:0]    count
);

    reg [3:0] count_reg;
    assign count = count_reg;

    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0000;
        end else if (load) begin
            count_reg <= data_in;
        end else if (up_down) begin
            count_reg <= count_reg + 4'b0001;
        end else begin
            count_reg <= count_reg - 4'b0001;
        end
    end
endmodule

module magnitude_comparator (
    input  wire [2:0]    a,
    input  wire [2:0]    b,
    input  wire        select,
    output wire [2:0]    comparison_result,
    output wire [1:0]    input_selected
);

    reg [2:0] comparison_result_reg;
    reg [1:0] input_selected_reg;
    assign comparison_result = comparison_result_reg;
    assign input_selected = input_selected_reg;

    always @(*) begin
        if (select == 1'b0) begin
            if (a > b) begin
                comparison_result_reg = 3'b001;
            end else if (a == b) begin
                comparison_result_reg = 3'b010;
            end else begin
                comparison_result_reg = 3'b100;
            end
            input_selected_reg = 2'b00;
        end else if (select == 1'b1) begin
            if (b > a) begin
                comparison_result_reg = 3'b001;
            end else if (a == b) begin
                comparison_result_reg = 3'b010;
            end else begin
                comparison_result_reg = 3'b100;
            end
            input_selected_reg = 2'b01;
        end else begin
            comparison_result_reg = 3'b000;
            input_selected_reg = 2'b00;
        end
    end
endmodule

module top_module (
    input  wire clk,
    input  wire up_down,
    input  wire load,
    input  wire reset,
    input  wire [2:0] a,
    input  wire [2:0] b,
    input  wire select,
    output wire [3:0] count,
    output wire [2:0] comparison_result,
    output wire [1:0] input_selected
);

    wire [3:0] count_wire;
    wire [2:0] comparison_result_wire;
    wire [1:0] input_selected_wire;

    up_down_counter counter (
        .clk(clk),
        .up_down(up_down),
        .load(load),
        .reset(reset),
        .data_in({a, 1'b0}),
        .count(count_wire)
    );

    magnitude_comparator comp (
        .a(a),
        .b(b),
        .select(select),
        .comparison_result(comparison_result_wire),
        .input_selected(input_selected_wire)
    );

    assign count = count_wire;
    assign comparison_result = comparison_result_wire;
    assign input_selected = input_selected_wire;
endmodule
