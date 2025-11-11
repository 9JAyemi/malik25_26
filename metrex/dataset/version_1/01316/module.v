module counter (
    input clk,
    input reset,
    output reg [3:0] count_out
);
    always @(posedge clk) begin
        if (reset) begin
            count_out <= 4'b0000;
        end else begin
            count_out <= count_out + 1;
        end
    end
endmodule

module mux (
    input [3:0] d,
    input [3:0] count_out,
    input select,
    output reg [3:0] mux_out
);
    always @(*) begin
        if (select) begin
            mux_out = d;
        end else begin
            mux_out = count_out;
        end
    end
endmodule

module adder (
    input [3:0] a,
    input [3:0] b,
    output reg [3:0] sum
);
    always @(*) begin
        sum = a + b;
    end
endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] d,
    input select,
    output [3:0] final_out
);
    wire [3:0] count_out;
    wire [3:0] mux_out;
    wire [3:0] adder_out;

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .count_out(count_out)
    );

    mux mux_inst (
        .d(d),
        .count_out(count_out),
        .select(select),
        .mux_out(mux_out)
    );

    adder adder_inst (
        .a(mux_out),
        .b(count_out),
        .sum(adder_out)
    );

    reg [3:0] final_out_reg;
    always @(posedge clk) begin
        final_out_reg <= adder_out;
    end

    assign final_out = final_out_reg;
endmodule