
module counter_combination (
    input wire clk,
    input wire reset,
    input wire [1:0] vec,
    output reg [3:0] outv,
    output reg o1,
    output reg o0
);

    reg [3:0] count_reg;
    wire [3:0] and_out;

    assign and_out = count_reg & {vec, 2'b00};

    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0000;
        end
        else begin
            count_reg <= count_reg + 1;
        end
    end

    always @(*) begin
        outv <= and_out;
        o1 <= and_out[3];
        o0 <= and_out[2];
    end

endmodule
module top_module ( 
    input wire clk,
    input wire reset,
    input wire [1:0] vec,
    output wire [3:0] outv,
    output wire o1,
    output wire o0,
    output wire [3:0] and_out,
    output wire [3:0] final_out
);

    wire [3:0] counter_out;
    wire [3:0] combination_out;

    counter_combination counter_combination_inst (
        .clk(clk),
        .reset(reset),
        .vec(vec),
        .outv(counter_out),
        .o1(o1),
        .o0(o0)
    );

    assign and_out = counter_out & vec;
    assign final_out = {~and_out[3:2], and_out[1:0]};
    assign outv = final_out;

endmodule